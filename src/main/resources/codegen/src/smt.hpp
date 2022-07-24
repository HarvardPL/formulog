#pragma once

#include <limits>
#include <vector>

#include "Term.hpp"

namespace flg {

using namespace std;

namespace smt {

enum class SmtStatus { sat, unsat, unknown };

struct SmtWorker;

struct SmtShim {
  SmtShim();
  SmtStatus check(const vector<term_ptr>& assertions,
                  int timeout=numeric_limits<int>::max());

  static bool needs_type_annotation(Symbol sym);
  static bool is_solver_var(Term* t);

  private:
  SmtWorker* worker;
};

inline thread_local SmtShim smt_shim;

} // namespace smt

using smt::SmtStatus;
using smt::smt_shim;

} // namespace flg
