//
// Created by Aaron Bembenek on 5/20/23.
//

#pragma once

#include <chrono>

namespace flg {

typedef std::chrono::duration<double, std::milli> time_t;

template<typename F>
time_t time(const F &f) {
    auto start = std::chrono::steady_clock::now();
    f();
    auto end = std::chrono::steady_clock::now();
    return std::chrono::duration_cast<time_t>(end - start);
}

}
