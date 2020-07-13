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

ostream& operator<<(ostream& out, Symbol sym) {
  switch (sym) {
    case Symbol::boxed_bool: return out << "boxed_bool";
    case Symbol::boxed_i32: return out << "boxed_i32";
    case Symbol::boxed_i64: return out << "boxed_i64";
    case Symbol::boxed_fp32: return out << "boxed_fp32";
    case Symbol::boxed_fp64: return out << "boxed_fp64";
    case Symbol::boxed_string: return out << "boxed_string";
/* INSERT 1 */
  }
  __builtin_unreachable();
}

map<string, Symbol> symbol_table;

void initialize_symbols() {
/* INSERT 2 */
}

Symbol lookup_symbol(const string& name) {
  auto it = symbol_table.find(name);
  if (it != symbol_table.end()) {
    return it->second;
  }
  cerr << "Unrecognized symbol: " << name << endl;
  abort();
}

Symbol lookup_tuple_symbol(size_t arity) {
  switch (arity) {
/* INSERT 3 */
    default:
    cerr << "Unrecognized tuple arity: " << arity << endl;
    abort();
  }
}

constexpr size_t symbol_arity(Symbol sym) {
  switch (sym) {
/* INSERT 4 */
    default: abort();
  }
}

} // namespace flg
