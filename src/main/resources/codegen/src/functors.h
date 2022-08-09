#pragma once

#include <souffle/SouffleInterface.h>
#include "Term.hpp"

namespace flg {

template<flg::Symbol S>
inline souffle::RamDomain dtor(const_term_ptr t) {
    return t->sym == S;
}

}

extern "C" {

souffle::RamDomain
nth(souffle::RamDomain n, souffle::RamDomain ref, souffle::RamDomain check);

/* INSERT 0 */

}