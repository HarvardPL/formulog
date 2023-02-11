#include "Symbol.hpp"

namespace flg {

ostream& operator<<(ostream& out, Symbol sym) {
  switch (sym) {
    case Symbol::boxed_bool: return out << "boxed_bool";
    case Symbol::boxed_i32: return out << "boxed_i32";
    case Symbol::boxed_i64: return out << "boxed_i64";
    case Symbol::boxed_fp32: return out << "boxed_fp32";
    case Symbol::boxed_fp64: return out << "boxed_fp64";
    case Symbol::boxed_string: return out << "boxed_string";
    case Symbol::model: return out << "model";
    case Symbol::opaque_set: return out << "opaque_set";
/* INSERT 0 */
  }
  __builtin_unreachable();
}

void initialize_symbols() {
/* INSERT 1 */
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
/* INSERT 2 */
    default:
    cerr << "Unrecognized tuple arity: " << arity << endl;
    abort();
  }
}

} // namespace flg
