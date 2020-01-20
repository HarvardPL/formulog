#pragma once

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

  private:
  bp::opstream z3_in;
  bp::ipstream z3_out;
  bp::child z3;
  map<const Term*, string, TermCompare> z3_vars;
  size_t cnt;

  void preprocess(const Term* assertion);
  void visit(const Term* assertion);
  void record_var(const Term* var);
  void declare_vars(ostream& out);
  string lookup_var(const Term* var);
	void serialize(const Term* assertion, ostream& out);
  void serialize(const std::string& op, const ComplexTerm& t, ostream& out);
  static bool needs_type_annotation(const Symbol& sym);
};

struct TypeInferer {
  vector<Type> inferType(const Term* t);

  private:
  vector<pair<Type, Type>> constraints;
  TypeSubst subst;

  vector<Type> inferType1(const Term* t);
};

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
  serialize(t, z3_in);
  //serialize(t, cout);
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

void SmtShim::visit(const Term* t) {
  switch (t->sym) {
    case Symbol::boxed_bool:
    case Symbol::boxed_i32:
    case Symbol::boxed_i64:
    case Symbol::boxed_fp32:
    case Symbol::boxed_fp64:
    case Symbol::boxed_string:
      break;
/* INSERT 1 */
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
  declare_vars(cout);
}

void SmtShim::declare_vars(ostream& out) {
  for (auto it = z3_vars.begin(); it != z3_vars.end(); it++) {
    out << "(declare-const " << it->second << " " <<
      Type::lookup(it->first->sym).second << ")" << endl;
  }
}

string SmtShim::lookup_var(const Term* t) {
  return z3_vars.find(t)->second;
}

void SmtShim::serialize(const Term* t, ostream& out) {
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
      if (x.arity > 0) {
        out << "(";
      }
      out << "|" << x.sym << "|";
      for (size_t i = 0; i < x.arity; ++i) {
        out << " ";
        serialize(x.val[i].get(), out); 
      }
      if (x.arity > 0) {
        out << ")";
      }
  }
}

void SmtShim::serialize(const std::string& op, const ComplexTerm& t, ostream& out) {
  size_t n = t.arity;
  if (n > 0) {
    out << "(";
  }
  out << op;
  for (size_t i = 0; i < n; ++i) {
    out << " ";
    serialize(t.val[i].get(), out);
  }
  if (n > 0) {
    out << ")";
  }
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
