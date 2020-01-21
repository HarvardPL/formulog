#pragma once

#include <bitset>
#include <boost/format.hpp>
#include <boost/process.hpp>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <map>

#include "Term.hpp"
#include "Type.hpp"

namespace flg {

using namespace std;
namespace bp = boost::process;

auto declarations = R"_(
/* INSERT 0 */
)_";

enum class SmtStatus { sat, unsat, unknown };

struct SmtShim {
  SmtShim();
  SmtStatus is_sat(const term_ptr& assertion);

  static bool needs_type_annotation(const Symbol& sym);
  static bool is_solver_var(const Term* t);

  private:
  bp::opstream z3_in;
  bp::ipstream z3_out;
  bp::child z3;
  map<const Term*, string, TermCompare> z3_vars;
  size_t cnt;
  vector<Type>::iterator annotations;

  void preprocess(const Term* assertion);
  void visit(const Term* assertion);
  void record_var(const Term* var);
  void declare_vars(ostream& out);
  string lookup_var(const Term* var);

  struct Serializer {
    Serializer(SmtShim& shim_, ostream& out_) : shim{shim_}, out{out_} {}
    void serialize(const Term* assertion);

    private:
    SmtShim& shim;
    ostream& out;

    void serialize(const std::string& repr, const ComplexTerm& t);
    template<size_t N> void serialize_bit_string(const int64_t val);
  };

};

struct TypeInferer {
  vector<Type> go(const Term* t);

  private:
  vector<Type> annotations;
  vector<pair<Type, Type>> constraints;
  TypeSubst subst;

  Type visit(const Term* t);
  void unify_constraints();
  void unify(const Type& ty1, const Type& ty2);
};

vector<Type> TypeInferer::go(const Term* t) {
  constraints.clear();
  subst.clear();
  annotations.clear();
  visit(t);
  unify_constraints();
  for (auto& type : annotations) {
    type = subst.apply(type);
  }
  return annotations;
}

Type TypeInferer::visit(const Term* t) {
  vector<Type> types;
  functor_type ft = Type::lookup(t->sym);
  if (SmtShim::needs_type_annotation(t->sym)) {
    annotations.push_back(ft.second);
  }
  if (!ft.first.empty()) {
    auto x = t->as_complex();
    if (!SmtShim::is_solver_var(t)) {
      for (size_t i = 0; i < x.arity; ++i) {
        constraints.push_back(make_pair(visit(x.val[i].get()), ft.first[i]));
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
  auto args1 = ty1.args;
  auto args2 = ty2.args;
  for (auto it1 = args1.begin(), it2 = args2.begin();
      it1 != args1.end(); it1++, it2++) {
    constraints.push_back(make_pair(*it1, *it2));
  }
}

SmtShim::SmtShim() :
  z3("z3 -in", bp::std_in < z3_in, (bp::std_out & bp::std_err) > z3_out) {
  z3_in << declarations << endl;
  z3_in << "(push)" << endl;
  z3_in.flush();
}

SmtStatus SmtShim::is_sat(const term_ptr& assertion) {
  z3_in << "(pop)";
  z3_in << "(push)";
  auto t = assertion.get();
  preprocess(t);
  z3_in << "(assert ";
  TypeInferer ti;
  auto types = ti.go(t);
  annotations = types.begin();
  Serializer{*this, z3_in}.serialize(t);
  assert(annotations == types.end()); 
  //annotations = types.begin();
  //Serializer{*this, cout}.serialize(t);
  //cout << endl;
  z3_in << ")" << endl;
  z3_in << "(check-sat)" << endl;
  z3_in.flush();
  string line;
  getline(z3_out, line);
  if (line == "sat") { 
    //cout << "sat" << endl;
    return SmtStatus::sat; 
  } else if (line == "unsat") {
    //cout << "unsat" << endl;
    return SmtStatus::unsat;
  } else if (line == "unknown") {
    //cout << "unknown" << endl;
    return SmtStatus::unknown;
  } else {
    cerr << "Unexpected Z3 response:" << endl;
    cerr << line << endl;
    abort();
  }
  __builtin_unreachable();
}

bool SmtShim::is_solver_var(const Term* t) {
  switch (t->sym) {
/* INSERT 1 */
    default:
      return false;
  }
}

void SmtShim::visit(const Term* t) {
  if (is_solver_var(t)) {
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
      auto x = t->as_complex();
      for (size_t i = 0; i < x.arity; ++i) {
        visit(x.val[i].get());
      }
  }
}

void SmtShim::record_var(const Term* t) {
  auto v = z3_vars.find(t);
  if (v == z3_vars.end()) {
    string name = "x" + to_string(cnt++);
    z3_vars.emplace(t, name);
  }
}

void SmtShim::preprocess(const Term* t) {
  z3_vars.clear();
  cnt = 0;
  visit(t);
  declare_vars(z3_in);
  //declare_vars(cout);
}

void SmtShim::declare_vars(ostream& out) {
  for (auto& e : z3_vars) {
    out << "(declare-const " << e.second << " " <<
      Type::lookup(e.first->sym).second << ")" << endl;
  }
}

string SmtShim::lookup_var(const Term* t) {
  return z3_vars.find(t)->second;
}

void SmtShim::Serializer::serialize(const Term* t) {
  switch (t->sym) {
    case Symbol::min_term:
    case Symbol::max_term:
      abort();
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
      auto val = t->as_base<float>().val;
      if (isnan(val)) {
        out << "(_ NaN 8 24)";
      } else if (isinf(val)) {
        if (val > 0) {
          out << "(_ +oo 8 24)";
        } else {
          out << "(_ -oo 8 24)";
        }
      } else {
        out << "((_ to_fp 8 24) RNE " << val << ")";
      }
      break;
    }
    case Symbol::boxed_fp64: {
      auto val = t->as_base<double>().val;
      if (isnan(val)) {
        out << "(_ NaN 11 53)";
      } else if (isinf(val)) {
        if (val > 0) {
          out << "(_ +oo 11 53)";
        } else {
          out << "(_ -oo 11 53)";
        }
      } else {
        out << "((_ to_fp 11 53) RNE " << val << ")";
      }
      break;
    }
/* INSERT 2 */
    default:
      auto x = t->as_complex();
      stringstream ss;
      ss << "|" << x.sym << "|";
      serialize(ss.str(), x);
  }
}

void SmtShim::Serializer::serialize(const std::string& repr, const ComplexTerm& t) {
  size_t n = t.arity;
  if (n > 0) {
    out << "(";
  }
  if (needs_type_annotation(t.sym)) {
    out << "(as " << repr << " " << *(shim.annotations++) << ")";
  } else {
    out << repr;
  }
  for (size_t i = 0; i < n; ++i) {
    out << " ";
    serialize(t.val[i].get());
  }
  if (n > 0) {
    out << ")";
  }
}

template<size_t N>
void SmtShim::Serializer::serialize_bit_string(const int64_t val) {
  out << bitset<N>(val).to_string;
}

bool SmtShim::needs_type_annotation(const Symbol& sym) {
  switch (sym) {
/* INSERT 3 */
    default:
      return false;
  }
}

thread_local SmtShim smt_shim;

} // namespace flg
