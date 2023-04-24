#pragma once

#include <souffle/SouffleInterface.h>
#include <tbb/combinable.h>
#include "smt_solver.h"

namespace flg::globals {

inline souffle::SouffleProgram *program{nullptr};

inline smt::SmtSolverMode smt_solver_mode{smt::SmtSolverMode::check_sat_assuming};

inline bool smt_double_check{true};

inline size_t smt_cache_size{100};

inline bool smt_stats{false};

inline tbb::combinable<unsigned long long> smt_calls;

inline tbb::combinable<unsigned long long> smt_time;

inline tbb::combinable<unsigned> smt_cache_clears;

template<typename T>
T sum(tbb::combinable<T> &stat) {
    return stat.combine([](T x, T y) -> T { return x + y; });
}

}