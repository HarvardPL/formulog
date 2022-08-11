//
// Created by Aaron Bembenek on 8/9/22.
//

#include "smt_solver.h"

namespace flg::smt {

TopLevelSmtSolver::TopLevelSmtSolver() {
    namespace bp = boost::process;
    bp::ipstream out;
    bp::opstream in;
    bp::child proc("z3 -in", bp::std_in < in, (bp::std_out & bp::std_err) > out);
    auto shim = std::make_unique<SmtLibShim>(std::move(proc), std::move(in), std::move(out));
    auto inner = std::make_unique<CheckSatAssumingSolver>(std::move(shim));
    m_delegate = std::make_unique<MemoizingSmtSolver>(std::move(inner));
}

SmtResult TopLevelSmtSolver::check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) {
    return m_delegate->check(assertions, get_model, timeout);
}

MemoizingSmtSolver::MemoizingSmtSolver(std::unique_ptr<SmtSolver> &&delegate) : m_delegate{std::move(delegate)} {}

void MemoizingSmtSolver::break_into_conjuncts(term_ptr t, sequenced_term_set &acc, bool negated) {
    if (t->sym == Symbol::smt_and && !negated) {
        auto &c = t->as_complex();
        break_into_conjuncts(c.val[0], acc);
        break_into_conjuncts(c.val[1], acc);
        return;
    } else if (t->sym == Symbol::smt_not || negated) {
        auto tt = t->as_complex().val[0];
        if (t->sym == Symbol::smt_not && negated) {
            break_into_conjuncts(tt, acc);
            return;
        }
        if (tt->sym == Symbol::smt_imp) {
            // Turn ~(A => B) into A /\ ~B
            auto &c = tt->as_complex();
            break_into_conjuncts(c.val[0], acc);
            break_into_conjuncts(c.val[1], acc, true);
            return;
        }
        if (tt->sym == Symbol::smt_or) {
            // Turn ~(A \/ B) into ~A /\ ~B
            auto &c = tt->as_complex();
            break_into_conjuncts(c.val[0], acc, true);
            break_into_conjuncts(c.val[1], acc, true);
            return;
        }
    }
    if (negated) {
#ifndef FLG_DEV
        t = Term::make<Symbol::smt_not>(t);
#endif
    }
    acc.push_back(t);
}

SmtResult MemoizingSmtSolver::check(const std::vector<term_ptr> &assertions, bool get_model, int timeout) {
    if (get_model) {
        throw std::runtime_error("not supporting models yet");
    }
    sequenced_term_set conjuncts;
    for (auto assertion: assertions) {
        break_into_conjuncts(assertion, conjuncts);
    }
    if (conjuncts.get<1>().find(Term::make(false)) != conjuncts.get<1>().end()) {
        return SmtResult::unsat;
    }
    conjuncts.remove(Term::make(true));
    if (conjuncts.empty()) {
        return SmtResult::sat;
    }
    std::vector key(conjuncts.get<0>().begin(), conjuncts.get<0>().end());
    SmtResult res;
    auto it = s_memo.find(key);
    if (it == s_memo.end()) {
        res = m_delegate->check(key, get_model, timeout);
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

}