#pragma once

#include <souffle/SouffleInterface.h>
#include "smt_solver.h"

namespace flg::globals {

extern souffle::SouffleProgram *program;

extern flg::smt::SmtSolverMode smt_solver_mode;

inline bool smt_double_check{true};

}