#include "globals.h"

namespace flg::globals {

souffle::SouffleProgram *program = nullptr;

flg::smt::SmtSolverMode smt_solver_mode{flg::smt::SmtSolverMode::check_sat_assuming};

}
