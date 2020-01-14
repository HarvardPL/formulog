#ifndef _SYMBOL_HPP__
#define _SYMBOL_HPP__

#include <cstdlib>
#include <iostream>

namespace flg {

enum class Symbol {
  min_term,
  boxed_bool,
  boxed_i32,
  boxed_i64,
  boxed_fp32,
  boxed_fp64,
  boxed_string,
/* INSERT 0 */
  max_term
};

std::ostream& operator<<(std::ostream& out, const Symbol& sym) {
	switch (sym) {
    case Symbol::min_term: return out << "min_term";
	  case Symbol::boxed_bool: return out << "boxed_bool";
	  case Symbol::boxed_i32: return out << "boxed_i32";
	  case Symbol::boxed_i64: return out << "boxed_i64";
	  case Symbol::boxed_fp32: return out << "boxed_fp32";
	  case Symbol::boxed_fp64: return out << "boxed_fp64";
	  case Symbol::boxed_string: return out << "boxed_string";
/* INSERT 1 */
    case Symbol::max_term: return out << "max_term";
	}
  __builtin_unreachable();
}

} // namespace flg

#endif
