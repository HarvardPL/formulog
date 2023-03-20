#pragma once

#include <souffle/SouffleInterface.h>
#include "smt_solver.h"

namespace flg::globals {

inline souffle::SouffleProgram *program{nullptr};

inline smt::SmtSolverMode smt_solver_mode{smt::SmtSolverMode::check_sat_assuming};

inline bool smt_double_check{true};

inline size_t smt_cache_size{100};

inline bool smt_stats{false};

inline std::atomic<unsigned long long> smt_calls;

inline std::atomic<unsigned long long> smt_time;

inline std::atomic<unsigned> smt_cache_clears;

}