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
  // >>> INSERT SYMBOLS <<<
};

} // namespace flg

#endif
