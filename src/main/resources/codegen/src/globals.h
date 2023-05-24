#pragma once

#include <souffle/SouffleInterface.h>
#include <tbb/combinable.h>
#include "smt_solver.h"
#include "time.hpp"

namespace flg::globals {

inline souffle::SouffleProgram *program{nullptr};

inline smt::SmtSolverMode smt_solver_mode{smt::SmtSolverMode::check_sat_assuming};

inline bool smt_double_check{true};

inline size_t smt_cache_size{100};

inline bool smt_stats{false};

struct smt_stats_t {
    time_t time;
    unsigned long long ncalls;

    friend smt_stats_t &operator+=(smt_stats_t &stats, time_t time) {
        stats.time += time;
        stats.ncalls++;
        return stats;
    }
};

inline tbb::combinable<smt_stats_t> smt_time;
inline tbb::combinable<time_t> smt_wait_time;
inline tbb::combinable<unsigned> smt_cache_hits;
inline tbb::combinable<unsigned> smt_cache_misses;
inline tbb::combinable<unsigned> smt_cache_clears;

template<typename T>
T sum(tbb::combinable<T> &stat) {
    return stat.combine([](T x, T y) -> T { return x + y; });
}

}