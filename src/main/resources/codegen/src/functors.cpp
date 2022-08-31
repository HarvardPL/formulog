#include "functors.h"
#include "funcs.hpp"

using namespace flg;
using namespace std;

souffle::RamDomain
nth(souffle::RamDomain n, souffle::RamDomain ref, souffle::RamDomain check) {
    assert(ref && check);
    return Term::unintize(ref)->as_complex().val[n]->intize();
}

/* INSERT 0 */