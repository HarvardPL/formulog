#pragma once

#include <cstdlib>
#include <iostream>
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

	void serialize(const term_ptr& assertion, ostream& out);
};

SmtShim::SmtShim() :
  z3("z3 -in", bp::std_in < z3_in, (bp::std_out & bp::std_err) > z3_out) {
  z3_in << declarations << endl;
  z3_in.flush();
}

SmtStatus SmtShim::is_sat(const term_ptr& assertion) {
  z3_in << "(assert ";
  serialize(assertion, z3_in);
  z3_in << ")" << endl;
  z3_in << "(check-sat)" << endl;
  z3_in.flush();
  string line;
  getline(z3_out, line);
  if (line == "sat") { 
    return SmtStatus::sat; 
  } else if (line == "unsat") {
    return SmtStatus::unsat;
  } else if (line == "unknown") {
    return SmtStatus::unknown;
  } else {
    cerr << "Unexpected Z3 response:" << endl;
    cerr << line << endl;
    abort();
  }
  __builtin_unreachable();
}

void SmtShim::serialize(const term_ptr& assertion, ostream& out) {
  out << "true" << endl;	
}

thread_local SmtShim smt_shim;

} // namespace flg
