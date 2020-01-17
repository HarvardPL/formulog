#pragma once

#include <cstdlib>
#include <iostream>
#include <boost/format.hpp>
#include <boost/process.hpp>

#include "Term.hpp"

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

	void serialize(const Term* assertion, ostream& out);
  void serialize(const std::string& op, const ComplexTerm& t, ostream& out);
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
  z3_in << "(assert ";
  serialize(assertion.get(), z3_in);
  //serialize(assertion.get(), cout);
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

void SmtShim::serialize(const Term* t, ostream& out) {
  switch (t->sym) {
    case Symbol::boxed_bool: {
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
/* INSERT 1 */
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

thread_local SmtShim smt_shim;

} // namespace flg
