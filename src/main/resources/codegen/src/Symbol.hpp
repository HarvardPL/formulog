#pragma once

#include <cstdlib>
#include <iostream>
#include <map>
#include <string>

namespace flg {

using namespace std;

enum class Symbol {
    boxed_bool,
    boxed_i32,
    boxed_i64,
    boxed_fp32,
    boxed_fp64,
    boxed_string,
/* INSERT 0 */
};

inline map<string, Symbol> symbol_table;

ostream &operator<<(ostream &out, Symbol sym);

void initialize_symbols();

Symbol lookup_symbol(const string &name);

Symbol lookup_tuple_symbol(size_t arity);

constexpr size_t symbol_arity(Symbol sym) {
    switch (sym) {
/* INSERT 1 */
        default:
            abort();
    }
#ifdef FLG_DEV
    return 0;
#endif
}

} // namespace flg
