#ifndef _SYMBOL_HPP__
#define _SYMBOL_HPP__

#include <cstdlib>
#include <string>

namespace flg {

enum class Symbol {
  boxed_i32,
  boxed_i64,
  boxed_fp32,
  boxed_fp64,
  boxed_string,
};

size_t symbol_arity(const Symbol& sym) {
  switch (sym) {
    case Symbol::boxed_i32:
    case Symbol::boxed_i64:
    case Symbol::boxed_fp32:
    case Symbol::boxed_fp64:
    case Symbol::boxed_string:
      std::abort();
  }
}

} // namespace flg

#endif
