//
// Created by Aaron Bembenek on 8/9/22.
//

#include "globals.h"
#include "smt_shim.h"
#include "smt_parser.hpp"
#include <bitset>
#include <boost/format.hpp>
#include <chrono>
#include <regex>

namespace flg::smt {

static const auto declarations = R"_(
/* INSERT 0 */
)_";

bool is_solver_var(term_ptr t) {
    switch (t->sym) {
/* INSERT 1 */
        default:
            return false;
    }
}

bool needs_type_annotation(Symbol sym) {
    switch (sym) {
/* INSERT 2 */
        default:
            return false;
    }
}

class MyTypeInferer {
public:
    std::deque<Type> go(term_ptr t);

private:
    std::deque<Type> m_annotations;
    std::vector<std::pair<Type, Type>> m_constraints;
    TypeSubst m_subst;

    Type visit(term_ptr t);

    void unify_constraints();

    void unify(const Type &ty1, const Type &ty2);
};

std::deque<Type> MyTypeInferer::go(term_ptr t) {
    m_constraints.clear();
    m_subst.clear();
    m_annotations.clear();
    visit(t);
    unify_constraints();
    for (auto &type: m_annotations) {
        type = m_subst.apply(type);
    }
    return m_annotations;
}

Type MyTypeInferer::visit(term_ptr t) {
    std::vector<Type> types;
    functor_type ft = Type::lookup(t->sym);
    if (needs_type_annotation(t->sym)) {
        m_annotations.push_back(ft.second);
    }
    if (!ft.first.empty()) {
        auto &x = t->as_complex();
        if (!is_solver_var(t)) {
            for (size_t i = 0; i < x.arity; ++i) {
                m_constraints.emplace_back(visit(x.val[i]), ft.first[i]);
            }
        }
    }
    return ft.second;
}

void MyTypeInferer::unify_constraints() {
    while (!m_constraints.empty()) {
        auto constraint = m_constraints.back();
        m_constraints.pop_back();
        auto ty1 = m_subst.apply(constraint.first);
        auto ty2 = m_subst.apply(constraint.second);
        if (ty1.is_var) {
            m_subst.put(ty1, ty2);
        } else if (ty2.is_var) {
            m_subst.put(ty2, ty1);
        } else {
            unify(ty1, ty2);
        }
    }
}

void MyTypeInferer::unify(const Type &ty1, const Type &ty2) {
    assert(ty1.name == ty2.name);
    auto args1 = ty1.args;
    auto args2 = ty2.args;
    for (auto it1 = args1.begin(), it2 = args2.begin();
         it1 != args1.end(); it1++, it2++) {
        m_constraints.emplace_back(*it1, *it2);
    }
}

SmtLibShim::SmtLibShim(boost::process::child &&proc, boost::process::opstream &&in, boost::process::ipstream &&out)
        : m_proc{std::move(proc)}, m_in{std::move(in)}, m_out{std::move(out)} {
            s_shims[this] = true;
        }

void SmtLibShim::declare_vars(term_ptr t) {
    if (is_solver_var(t)) {
        if (m_solver_vars.find(t) == m_solver_vars.end()) {
            std::stringstream ss;
            ss << "x" << m_cnt++;
            auto s = ss.str();
            m_solver_vars.emplace(t, s);
            m_solver_var_lookup.emplace(s, t);
            m_solver_vars_in_order.push_back(t);
            m_in << "(declare-fun " << s << " () " << Type::lookup(t->sym).second << ")\n";
        }
        return;
    }
    switch (t->sym) {
        case Symbol::boxed_bool:
        case Symbol::boxed_i32:
        case Symbol::boxed_i64:
        case Symbol::boxed_fp32:
        case Symbol::boxed_fp64:
        case Symbol::boxed_string:
            break;
        default:
            auto &x = t->as_complex();
            for (size_t i = 0; i < x.arity; ++i) {
                declare_vars(x.val[i]);
            }
    }
}

void SmtLibShim::make_declarations() {
    m_in << declarations << "\n";
}

void SmtLibShim::push() {
    m_in << "(push 1)\n";
    m_stack_positions.push_back(m_solver_vars_in_order.size());
}

void SmtLibShim::pop(unsigned int n) {
    m_in << "(pop " << n << ")\n";
    if (n > 0) {
        unsigned int stack_pos = m_stack_positions.size() - n;
        unsigned int start_pos = m_stack_positions[stack_pos];
        m_stack_positions.erase(m_stack_positions.begin() + stack_pos, m_stack_positions.end());
        unsigned int how_many = m_solver_vars_in_order.size() - start_pos;
        for (unsigned int i = 0; i < how_many; ++i) {
            auto var = m_solver_vars_in_order.back();
            auto symbol = m_solver_vars[var];
            m_solver_vars.erase(var);
            m_solver_var_lookup.erase(symbol);
            m_solver_vars_in_order.pop_back();
        }
    }
}

void SmtLibShim::make_assertion(term_ptr assertion) {
    declare_vars(assertion);
    m_annotations = MyTypeInferer().go(assertion);
    m_in << "(assert ";
    serialize(assertion);
    m_in << ")\n";
    assert(m_annotations.empty());
}

SmtStatus SmtLibShim::check_sat_assuming(const std::vector<term_ptr> &onVars, const std::vector<term_ptr> &offVars,
                                         int timeout) {
    if (timeout < 0) {
        cerr << "Warning: ignoring negative timeout provided to SMT" << endl;
        timeout = numeric_limits<int>::max();
    }
    m_in << "(set-option :timeout " << timeout << ")\n";

    if (onVars.empty() && offVars.empty()) {
        m_in << "(check-sat)\n";
    } else {
        m_in << "(check-sat-assuming (";
        for (auto var: onVars) {
            m_in << lookup_var(var) << " ";
        }
        for (auto var: offVars) {
            m_in << "(not " << lookup_var(var) << ") ";
        }
        m_in << "))\n";
    }
    m_in.flush();

    std::chrono::time_point<std::chrono::steady_clock> start;
    if (globals::smt_stats) {
        start = std::chrono::steady_clock::now();
    }
    string line;
    getline(m_out, line);
    if (globals::smt_stats) {
        auto end = std::chrono::steady_clock::now();
        globals::smt_time += chrono::duration_cast<chrono::milliseconds>(end - start).count();
        globals::smt_calls++;
    }
    SmtStatus status;
    if (line == "sat") {
        status = SmtStatus::sat;
    } else if (line == "unsat") {
        status = SmtStatus::unsat;
    } else if (line == "unknown") {
        status = SmtStatus::unknown;
    } else {
        cerr << "Unexpected SMT response:" << endl;
        cerr << line << endl;
        abort();
    }
    return status;
}

Model SmtLibShim::get_model() {
    m_in << "(get-model)\n";
    m_in.flush();
    SmtLibParser parser(m_solver_var_lookup);
    return parser.get_model(m_out);
}

void SmtLibShim::serialize(term_ptr t) {
    switch (t->sym) {
        case Symbol::boxed_bool: {
            m_in << *t;
            break;
        }
        case Symbol::boxed_string: {
            m_in << "\"" << std::regex_replace(t->as_base<std::string>().val, std::regex("\""), "\"\"") << "\"";
            break;
        }
        case Symbol::boxed_i32: {
            m_in << "#x" << boost::format{"%08x"} % t->as_base<int32_t>().val;
            break;
        }
        case Symbol::boxed_i64: {
            m_in << "#x" << boost::format{"%016x"} % t->as_base<int64_t>().val;
            break;
        }
        case Symbol::boxed_fp32: {
            serialize_fp<float, 8, 24>(t);
            break;
        }
        case Symbol::boxed_fp64: {
            serialize_fp<double, 11, 53>(t);
            break;
        }
/* INSERT 3 */
        default:
            auto &x = t->as_complex();
            stringstream ss;
            serialize(serialize_sym(x.sym), x);
    }
}

void SmtLibShim::serialize(const std::string &repr, const ComplexTerm &t) {
    size_t n = t.arity;
    if (n > 0) {
        m_in << "(";
    }
    if (needs_type_annotation(t.sym)) {
        m_in << "(as " << repr << " " << next_annotation() << ")";
    } else {
        m_in << repr;
    }
    for (size_t i = 0; i < n; ++i) {
        m_in << " ";
        serialize(t.val[i]);
    }
    if (n > 0) {
        m_in << ")";
    }
}

template<typename T, size_t N>
void SmtLibShim::serialize_bit_string(T val) {
    m_in << "#b" << std::bitset<N>(val).to_string();
}

template<size_t From, size_t To, bool Signed>
void SmtLibShim::serialize_bv_to_bv(term_ptr t) {
    auto arg = arg0(t);
    if (From < To) {
        m_in << "((_ " << (Signed ? "sign" : "zero") << "_extend "
             << (To - From) << ") ";
        serialize(arg);
        m_in << ")";
    } else if (From > To) {
        m_in << "((_ extract " << (To - 1) << " 0) ";
        serialize(arg);
        m_in << ")";
    } else {
        serialize(arg);
    }
}

void SmtLibShim::serialize_bv_extract(term_ptr t) {
    m_in << "((_ extract " << *argn(t, 2) << " " << *argn(t, 1) << ") ";
    serialize(arg0(t));
    m_in << ")";
}

template<size_t E, size_t S>
void SmtLibShim::serialize_bv_to_fp(term_ptr t) {
    m_in << "((_ to_fp " << E << " " << S << ") RNE ";
    serialize(arg0(t));
    m_in << ")";
}

template<typename T, size_t E, size_t S>
void SmtLibShim::serialize_fp(term_ptr t) {
    auto val = t->as_base<T>().val;
    stringstream ss;
    ss << E << " " << S;
    auto s = ss.str();
    if (isnan(val)) {
        m_in << "(_ NaN " << s << ")";
    } else if (isinf(val)) {
        if (val > 0) {
            m_in << "(_ +oo " << s << ")";
        } else {
            m_in << "(_ -oo " << s << ")";
        }
    } else {
        m_in << "((_ to_fp " << s << ") RNE " << val << ")";
    }
}

template<size_t N, bool Signed>
void SmtLibShim::serialize_fp_to_bv(term_ptr t) {
    m_in << "((_ " << (Signed ? "fp.to_sbv" : "fp.to_ubv") << " " << N << ") RNE ";
    serialize(arg0(t));
    m_in << ")";
}

template<size_t E, size_t S>
void SmtLibShim::serialize_fp_to_fp(term_ptr t) {
    m_in << "((_ to_fp " << E << " " << S << ") RNE ";
    serialize(arg0(t));
    m_in << ")";
}

void SmtLibShim::serialize_let(term_ptr t) {
    auto &x = t->as_complex();
    m_in << "(let ((";
    serialize(x.val[0]);
    m_in << " ";
    serialize(x.val[1]);
    m_in << ")) ";
    serialize(x.val[2]);
    m_in << ")";
}

template<typename T>
void SmtLibShim::serialize_int(term_ptr t) {
    m_in << arg0(t)->as_base<T>().val;
}

template<size_t W>
void SmtLibShim::serialize_int2bv(term_ptr t) {
    m_in << "((_ int2bv " << W << ") ";
    serialize(arg0(t));
    m_in << ")";
}

template<bool Exists>
void SmtLibShim::serialize_quantifier(term_ptr t) {
    auto &x = t->as_complex();
    m_in << "(" << (Exists ? "exists (" : "forall (");
    for (auto &v: Term::vectorize_list_term(x.val[0])) {
        // Consume annotation for cons
        next_annotation();
        auto var = arg0(v);
        m_in << "(";
        serialize(var);
        m_in << " " << Type::lookup(var->sym).second << ")";
    }
    m_in << ") ";
    // Consume annotation for nil
    next_annotation();
    auto pats = Term::vectorize_list_term(x.val[2]);
    if (!pats.empty()) {
        m_in << "(! ";
    }
    serialize(x.val[1]);
    if (!pats.empty()) {
        for (auto &pat: pats) {
            m_in << " :pattern (";
            // Consume annotation for cons
            next_annotation();
            bool first{true};
            for (auto &sub: Term::vectorize_list_term(pat)) {
                if (!first) {
                    m_in << " ";
                }
                first = false;
                // Consume annotation for cons
                next_annotation();
                serialize(arg0(sub));
            }
            m_in << ")";
            // Consume annotation for nil
            next_annotation();
        }
        m_in << ")";
    }
    // Consume annotation for nil
    next_annotation();
    m_in << ")";
}

string SmtLibShim::serialize_sym(Symbol sym) {
    switch (sym) {
/* INSERT 4 */
        default:
            stringstream ss;
            ss << "|" << sym << "|";
            return ss.str();
    }
}

string SmtLibShim::serialize_tester(Symbol sym) {
    stringstream ss;
    ss << sym;
    string s = ss.str().substr(4, string::npos);
    return "|is-" + s + "|";
}

}