#pragma once

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
  bp::opstream in;
  bp::ipstream out;
  bp::ipstream err;
  bp::child z3;

	void serialize(const term_ptr& assertion, ostream& out);
};

SmtShim::SmtShim() :
  z3("z3 -in", bp::std_in < in, bp::std_out > out, bp::std_err > err) {
  in << declarations << endl;
  in.flush();
}

SmtStatus SmtShim::is_sat(const term_ptr& assertion) {
  return SmtStatus::sat;
}

void SmtShim::serialize(const term_ptr& assertion, ostream& out) {
  out << "(true)" << endl;	
}

thread_local SmtShim smt_shim;

} // namespace flg
