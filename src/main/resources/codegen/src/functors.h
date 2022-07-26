#pragma once

#include <souffle/SouffleInterface.h>
#include "Term.hpp"

namespace flg {

template<flg::Symbol S>
souffle::RamDomain dtor(souffle::RecordTable *rt, const_term_ptr t) {
    auto &c = t->as_complex();
    if (c.sym == S) {
        auto tup = new souffle::RamDomain[c.arity];
        for (size_t i = 0; i < c.arity; ++i) {
            tup[i] = c.val[i]->intize();
        }
        return rt->pack(tup, c.arity);
    }
    return 0;
}

}

extern "C" {

souffle::RamDomain
nth(souffle::SymbolTable *st, souffle::RecordTable *rt, souffle::RamDomain n, souffle::RamDomain ref,
    souffle::RamDomain arity);

/* INSERT 0 */

}