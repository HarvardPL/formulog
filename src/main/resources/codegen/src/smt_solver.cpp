//
// Created by Aaron Bembenek on 8/9/22.
//

#include "globals.h"
#include "smt_solver.h"

namespace flg::smt {

TopLevelSmtSolver::TopLevelSmtSolver() {
    std::unique_ptr<SmtSolver> inner;
    switch (globals::smt_solver_mode) {
        case SmtSolverMode::push_pop_naive:
            inner = std::make_unique<PushPopNaiveSolver>(make_shim());
            break;
        case SmtSolverMode::push_pop:
            inner = std::make_unique<PushPopSolver>(make_shim());
            break;
        case SmtSolverMode::check_sat_assuming:
            inner = std::make_unique<CheckSatAssumingSolver>(make_shim());
            if (globals::smt_double_check) {
                auto checker = std::make_unique<PushPopSolver>(make_shim());
                inner = std::make_unique<DoubleCheckingSolver>(std::move(inner), std::move(checker));
            }
            break;
    }
    m_delegate = std::make_unique<MemoizingSmtSolver>(std::move(inner));
}

std::unique_ptr<SmtShim> TopLevelSmtSolver::make_shim() {
    namespace bp = boost::process;
    bp::ipstream out;
    bp::opstream in;
    bp::child proc("z3 -in", bp::std_in < in, (bp::std_out & bp::std_err) > out);
    return std::make_unique<SmtLibShim>(std::move(proc), std::move(in), std::move(out));
}

SmtResult TopLevelSmtSolver::check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) {
    return m_delegate->check(assertions, get_model, timeout);
}

MemoizingSmtSolver::MemoizingSmtSolver(std::unique_ptr<SmtSolver> &&delegate) : m_delegate{std::move(delegate)} {}

void MemoizingSmtSolver::break_into_conjuncts(term_ptr t, std::set<term_ptr> &unordered, std::vector<term_ptr> &ordered,
                                              bool negated) {
    if (t->sym == Symbol::smt_and && !negated) {
        auto &c = t->as_complex();
        break_into_conjuncts(c.val[0], unordered, ordered);
        break_into_conjuncts(c.val[1], unordered, ordered);
        return;
    } else if (t->sym == Symbol::smt_not || negated) {
        auto tt = t->as_complex().val[0];
        if (t->sym == Symbol::smt_not && negated) {
            break_into_conjuncts(tt, unordered, ordered);
            return;
        }
        if (tt->sym == Symbol::smt_imp) {
            // Turn ~(A => B) into A /\ ~B
            auto &c = tt->as_complex();
            break_into_conjuncts(c.val[0], unordered, ordered);
            break_into_conjuncts(c.val[1], unordered, ordered, true);
            return;
        }
        if (tt->sym == Symbol::smt_or) {
            // Turn ~(A \/ B) into ~A /\ ~B
            auto &c = tt->as_complex();
            break_into_conjuncts(c.val[0], unordered, ordered, true);
            break_into_conjuncts(c.val[1], unordered, ordered, true);
            return;
        }
    }
    if (negated) {
#ifndef FLG_DEV
        t = Term::make<Symbol::smt_not>(t);
#endif
    }
    if (t != Term::make(true)) {
        auto it = unordered.insert(t);
        if (it.second) {
            ordered.push_back(t);
        }
    }
}

SmtResult MemoizingSmtSolver::check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) {
    if (get_model) {
        throw std::runtime_error("not supporting models yet");
    }
    std::vector<term_ptr> conjuncts;
    std::set<term_ptr> key;
    for (auto assertion: assertions) {
        break_into_conjuncts(assertion, key, conjuncts);
    }
    if (conjuncts.empty()) {
        return SmtResult::sat;
    }
    if (key.find(Term::make(false)) != key.end()) {
        return SmtResult::unsat;
    }
    SmtResult res;
    auto it = s_memo.find(key);
    if (it == s_memo.end()) {
        res = m_delegate->check(conjuncts, get_model, timeout);
        auto p = s_memo.emplace(key, res);
        if (!p.second) {
            res = p.first->second;
        }
    } else {
        res = it->second;
    }
    return res;
}

SmtResult AbstractSmtSolver::check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) {
    if (get_model) {
        throw std::runtime_error("not supporting models yet");
    }
    if (!m_initialized) {
        initialize();
        m_initialized = true;
    }
    term_vector_pair p = make_assertions(assertions);
    auto res = m_shim->check_sat_assuming(p.first, p.second, timeout);
    cleanup();
    return res;
}

void PushPopNaiveSolver::initialize() {
    m_shim->make_declarations();
}

AbstractSmtSolver::term_vector_pair PushPopNaiveSolver::make_assertions(const std::vector<term_ptr> &assertions) {
    m_shim->push();
    for (auto assertion: assertions) {
        m_shim->make_assertion(assertion);
    }
    return {{},
            {}};
}

void PushPopNaiveSolver::cleanup() {
    m_shim->pop(1);
}

void CheckSatAssumingSolver::initialize() {
    m_shim->make_declarations();
}

AbstractSmtSolver::term_vector_pair CheckSatAssumingSolver::make_assertions(const std::vector<term_ptr> &assertions) {
    std::vector<term_ptr> on_vars;
    for (auto assertion: assertions) {
        auto &var = m_conjuncts_to_vars[assertion];
        if (!var) {
            var = ComplexTerm::fresh_smt_var();
        }
        on_vars.emplace_back(var);
#ifdef FLG_DEV
        auto imp = nullptr;
#else
        auto imp = Term::make<Symbol::smt_imp>(var, assertion);
#endif
        m_shim->make_assertion(imp);
    }
    return {on_vars,
            {}};
}

void CheckSatAssumingSolver::cleanup() {
    // do nothing
}

void PushPopSolver::initialize() {
    m_shim->make_declarations();
}

AbstractSmtSolver::term_vector_pair PushPopSolver::make_assertions(const std::vector<term_ptr> &assertions) {
    unsigned int pos = find_diff_pos(assertions);
    shrink_cache(m_set.size() - pos);
    assert(m_stack.size() == pos && m_set.size() == pos);
    assert(pos <= assertions.size());
    for (auto it = assertions.begin() + pos; it != assertions.end(); ++it) {
        auto elt = *it;
        if (m_set.insert(elt).second) {
            m_shim->push();
            m_shim->make_assertion(elt);
            m_stack.push_back(elt);
        }
    }
    assert(m_stack.size() == m_set.size());
    assert(m_stack.size() <= assertions.size());
    return {{},
            {}};
}

void PushPopSolver::cleanup() {
    // do nothing
}

unsigned int PushPopSolver::find_diff_pos(const std::vector<term_ptr> &assertions) {
    unsigned int pos = 0;
    unsigned int end = std::min(m_stack.size(), assertions.size());
    while (pos < end) {
        auto assertion = assertions[pos];
        if (m_set.find(assertion) == m_set.end() && m_stack[pos] != assertion) {
            break;
        }
        pos++;
    }
    return pos;
}

void PushPopSolver::shrink_cache(unsigned int num_to_pop) {
    m_shim->pop(num_to_pop);
    for (unsigned int i = 0; i < num_to_pop; ++i) {
        m_set.erase(m_stack.back());
        m_stack.pop_back();
    }
}

SmtResult DoubleCheckingSolver::check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) {
    auto res = m_first->check(assertions, get_model, timeout);
    if (res == SmtResult::unknown) {
        res = m_second->check(assertions, get_model, timeout);
    }
    return res;
}

}