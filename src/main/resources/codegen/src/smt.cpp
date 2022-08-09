#include <bitset>
#include <cassert>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <map>
#include <sstream>
#include <string>

#include <boost/format.hpp>
#include <boost/process.hpp>

#include "Type.hpp"
#include "smt.hpp"

namespace flg::smt {

namespace bp = boost::process;

static const auto declarations = R"_(
/* INSERT 0 */
)_";

struct SmtWorker {
    SmtWorker();

    SmtStatus check(const linked_term_set &assertions,
                    int timeout = numeric_limits<int>::max());

private:
    bp::opstream z3_in;
    bp::ipstream z3_out;
    bp::child z3;
    map<term_ptr, string> z3_vars;
    size_t cnt;
    vector<Type>::iterator annotations;

    void preprocess(const linked_term_set &assertions);

    void visit(term_ptr t);

    void record_var(term_ptr var);

    void declare_vars(ostream &out);

    string lookup_var(term_ptr var);

    struct Serializer {
        Serializer(SmtWorker &shim_, ostream &out_) : shim{shim_}, out{out_} {}

        void serialize(term_ptr assertion);

    private:
        SmtWorker &shim;
        ostream &out;

        static term_ptr arg0(term_ptr t);

        static term_ptr argn(term_ptr t, size_t n);

        void serialize(const std::string &repr, const ComplexTerm &t);

        template<typename T, size_t N>
        void serialize_bit_string(T val);

        template<size_t From, size_t To, bool Signed>
        void serialize_bv_to_bv(term_ptr t);

        void serialize_bv_extract(term_ptr t);

        template<size_t E, size_t S>
        void serialize_bv_to_fp(term_ptr t);

        template<typename T, size_t E, size_t S>
        void serialize_fp(term_ptr t);

        template<size_t N, bool Signed>
        void serialize_fp_to_bv(term_ptr t);

        template<size_t S, size_t E>
        void serialize_fp_to_fp(term_ptr t);

        void serialize_let(term_ptr t);

        template<typename T>
        void serialize_int(term_ptr t);

        template<bool Exists>
        void serialize_quantifier(term_ptr t);

        string serialize_sym(Symbol sym);

        string serialize_tester(Symbol sym);
    };

};

struct TypeInferer {
    vector<Type> go(term_ptr t);

private:
    vector<Type> annotations;
    vector<pair<Type, Type>> constraints;
    TypeSubst subst;

    Type visit(term_ptr t);

    void unify_constraints();

    void unify(const Type &ty1, const Type &ty2);
};

SmtShim::SmtShim() : worker(new SmtWorker) {}

SmtStatus SmtShim::check(const vector<term_ptr> &assertions, int timeout) {
    linked_term_set conjuncts;
    for (auto assertion: assertions) {
        break_into_conjuncts(assertion, conjuncts);
    }
    unordered_set<term_ptr> s(conjuncts.begin(), conjuncts.end());
    if (conjuncts.get<1>().find(Term::make(false)) != conjuncts.get<1>().end()) {
        return SmtStatus::unsat;
    }
    conjuncts.remove(Term::make(true));
    if (conjuncts.empty()) {
        return SmtStatus::sat;
    }
    set key(conjuncts.get<0>().begin(), conjuncts.get<0>().end());
    SmtStatus res;
    auto it = s_memo.find(key);
    if (it == s_memo.end()) {
        res = worker->check(conjuncts, timeout);
        auto p = s_memo.emplace(key, res);
        if (!p.second) {
            res = p.first->second;
        }
    } else {
        res = it->second;
    }
    return res;
}

void SmtShim::break_into_conjuncts(term_ptr t, linked_term_set &acc, bool negated) {
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

bool SmtShim::is_solver_var(term_ptr t) {
    switch (t->sym) {
/* INSERT 1 */
        default:
            return false;
    }
}

bool SmtShim::needs_type_annotation(Symbol sym) {
  switch (sym) {
/* INSERT 2 */
    default:
      return false;
  }
}

vector<Type> TypeInferer::go(term_ptr t) {
    constraints.clear();
    subst.clear();
    annotations.clear();
    visit(t);
    unify_constraints();
    for (auto &type: annotations) {
        type = subst.apply(type);
    }
    return annotations;
}

Type TypeInferer::visit(term_ptr t) {
    vector<Type> types;
    functor_type ft = Type::lookup(t->sym);
    if (SmtShim::needs_type_annotation(t->sym)) {
        annotations.push_back(ft.second);
    }
    if (!ft.first.empty()) {
        auto &x = t->as_complex();
        if (!SmtShim::is_solver_var(t)) {
            for (size_t i = 0; i < x.arity; ++i) {
                constraints.push_back(make_pair(visit(x.val[i]), ft.first[i]));
            }
        }
    }
    return ft.second;
}

void TypeInferer::unify_constraints() {
  while (!constraints.empty()) {
    auto constraint = constraints.back();
    constraints.pop_back();
    auto ty1 = subst.apply(constraint.first);
    auto ty2 = subst.apply(constraint.second);
    if (ty1.is_var) {
      subst.put(ty1, ty2);
    } else if (ty2.is_var) {
      subst.put(ty2, ty1);
    } else {
      unify(ty1, ty2);
    }
  }
}

void TypeInferer::unify(const Type& ty1, const Type& ty2) {
  assert(ty1.name == ty2.name);
  auto args1 = ty1.args;
  auto args2 = ty2.args;
  for (auto it1 = args1.begin(), it2 = args2.begin();
      it1 != args1.end(); it1++, it2++) {
    constraints.push_back(make_pair(*it1, *it2));
  }
}

SmtWorker::SmtWorker() :
  z3("z3 -in", bp::std_in < z3_in, (bp::std_out & bp::std_err) > z3_out) {
  z3_in << declarations << endl;
  z3_in << "(push)" << endl;
  z3_in.flush();
}

SmtStatus SmtWorker::check(const linked_term_set &assertions, int timeout) {
    z3_in << "(pop)" << endl;
    z3_in << "(push)" << endl;
    if (timeout < 0) {
        cerr << "Warning: negative timeout provided to Z3 - ignored" << endl;
        timeout = numeric_limits<int>::max();
    }
    z3_in << "(set-option :timeout " << timeout << ")" << endl;

    preprocess(assertions);
    TypeInferer ti;
    for (term_ptr t: assertions) {
        z3_in << "(assert ";
        auto types = ti.go(t);
        annotations = types.begin();
        Serializer{*this, z3_in}.serialize(t);
        assert(annotations == types.end());
        z3_in << ")" << endl;
    }

    z3_in << "(check-sat)" << endl;
    z3_in.flush();
    string line;
    getline(z3_out, line);
    SmtStatus res;
    if (line == "sat") {
        res = SmtStatus::sat;
    } else if (line == "unsat") {
        res = SmtStatus::unsat;
    } else if (line == "unknown") {
        res = SmtStatus::unknown;
    } else {
        cerr << "Unexpected Z3 response:" << endl;
        cerr << line << endl;
        abort();
    }
    return res;
}

void SmtWorker::visit(term_ptr t) {
    if (SmtShim::is_solver_var(t)) {
        record_var(t);
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
                visit(x.val[i]);
            }
    }
}

void SmtWorker::record_var(term_ptr var) {
    auto v = z3_vars.find(var);
    if (v == z3_vars.end()) {
        string name = "x" + to_string(cnt++);
        z3_vars.emplace(var, name);
    }
}

void SmtWorker::preprocess(const linked_term_set &assertions) {
    z3_vars.clear();
    cnt = 0;
    for (auto t: assertions) {
        visit(t);
    }
    declare_vars(z3_in);
}

void SmtWorker::declare_vars(ostream& out) {
  for (auto& e : z3_vars) {
    out << "(declare-const " << e.second << " " <<
      Type::lookup(e.first->sym).second << ")" << endl;
  }
}

string SmtWorker::lookup_var(term_ptr t) {
    return z3_vars.find(t)->second;
}

term_ptr SmtWorker::Serializer::arg0(term_ptr t) {
    return t->as_complex().val[0];
}

term_ptr SmtWorker::Serializer::argn(term_ptr t, size_t n) {
    return t->as_complex().val[n];
}

void SmtWorker::Serializer::serialize(term_ptr t) {
    switch (t->sym) {
        case Symbol::boxed_bool:
        case Symbol::boxed_string: {
            out << *t;
            break;
        }
        case Symbol::boxed_i32: {
            out << "#x" << boost::format{"%08x"} % t->as_base<int32_t>().val;
            break;
        }
        case Symbol::boxed_i64: {
            out << "#x" << boost::format{"%016x"} % t->as_base<int64_t>().val;
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

void SmtWorker::Serializer::serialize(const std::string& repr, const ComplexTerm& t) {
  size_t n = t.arity;
  if (n > 0) {
    out << "(";
  }
  if (SmtShim::needs_type_annotation(t.sym)) {
    out << "(as " << repr << " " << *(shim.annotations++) << ")";
  } else {
    out << repr;
  }
  for (size_t i = 0; i < n; ++i) {
    out << " ";
    serialize(t.val[i]);
  }
  if (n > 0) {
    out << ")";
  }
}

template<typename T, size_t N>
void SmtWorker::Serializer::serialize_bit_string(T val) {
    out << "#b" << bitset<N>(val).to_string();
}

template<size_t From, size_t To, bool Signed>
void SmtWorker::Serializer::serialize_bv_to_bv(term_ptr t) {
    auto arg = arg0(t);
    if (From < To) {
        out << "((_ " << (Signed ? "sign" : "zero") << "_extend "
            << (To - From) << ") ";
        serialize(arg);
        out << ")";
    } else if (From > To) {
        out << "((_ extract " << (To - 1) << " 0) ";
        serialize(arg);
        out << ")";
    } else {
        serialize(arg);
    }
}

void SmtWorker::Serializer::serialize_bv_extract(term_ptr t) {
    out << "((_ extract " << *argn(t, 2) << " " << *argn(t, 1) << ") ";
    serialize(arg0(t));
    out << ")";
}

template<size_t E, size_t S>
void SmtWorker::Serializer::serialize_bv_to_fp(term_ptr t) {
    out << "((_ to_fp " << E << " " << S << ") RNE ";
    serialize(arg0(t));
    out << ")";
}

template<typename T, size_t E, size_t S>
void SmtWorker::Serializer::serialize_fp(term_ptr t) {
    auto val = t->as_base<T>().val;
    stringstream ss;
    ss << E << " " << S;
    auto s = ss.str();
    if (isnan(val)) {
        out << "(_ NaN " << s << ")";
    } else if (isinf(val)) {
        if (val > 0) {
            out << "(_ +oo " << s << ")";
        } else {
            out << "(_ -oo " << s << ")";
        }
    } else {
        out << "((_ to_fp " << s << ") RNE " << val << ")";
    }
}

template<size_t N, bool Signed>
void SmtWorker::Serializer::serialize_fp_to_bv(term_ptr t) {
    out << "((_ " << (Signed ? "fp.to_sbv" : "fp.to_ubv") << " " << N << ") RNE ";
    serialize(arg0(t));
    out << ")";
}

template<size_t E, size_t S>
void SmtWorker::Serializer::serialize_fp_to_fp(term_ptr t) {
    out << "((_ to_fp " << E << " " << S << ") RNE ";
    serialize(arg0(t));
    out << ")";
}

void SmtWorker::Serializer::serialize_let(term_ptr t) {
    auto &x = t->as_complex();
    out << "(let ((";
    serialize(x.val[0]);
    out << " ";
    serialize(x.val[1]);
    out << ")) ";
    serialize(x.val[2]);
    out << ")";
}

template<typename T>
void SmtWorker::Serializer::serialize_int(term_ptr t) {
    out << arg0(t)->as_base<T>().val;
}

template<bool Exists>
void SmtWorker::Serializer::serialize_quantifier(term_ptr t) {
    auto &x = t->as_complex();
    out << "(" << (Exists ? "exists (" : "forall (");
    for (auto &v: Term::vectorize_list_term(x.val[0])) {
        // Consume annotation for cons
        shim.annotations++;
        auto var = arg0(v);
        out << "(";
        serialize(var);
        out << " " << Type::lookup(var->sym).second << ")";
    }
    out << ") ";
    // Consume annotation for nil
    shim.annotations++;
    auto pats = Term::vectorize_list_term(x.val[2]);
    if (!pats.empty()) {
        out << "(! ";
    }
    serialize(x.val[1]);
    if (!pats.empty()) {
        for (auto &pat: pats) {
      out << " :pattern (";
      // Consume annotation for cons
      shim.annotations++;
      bool first{true};
      for (auto& sub : Term::vectorize_list_term(pat)) {
        if (!first) {
          out << " ";
        }
        first = false;
        // Consume annotation for cons
        shim.annotations++;
        serialize(arg0(sub));
      }
      out << ")";
      // Consume annotation for nil
      shim.annotations++;
    }
    out << ")";
  }
  // Consume annotation for nil
  shim.annotations++;
  out << ")";
}

string SmtWorker::Serializer::serialize_sym(Symbol sym) {
  switch (sym) {
/* INSERT 4 */
    default:
      stringstream ss;
      ss << "|" << sym << "|";
      return ss.str();
  }
}

string SmtWorker::Serializer::serialize_tester(Symbol sym) {
  stringstream ss;
  ss << sym;
  string s = ss.str().substr(4, string::npos);
  return "|is-" + s + "|";
}

} // namespace flg
