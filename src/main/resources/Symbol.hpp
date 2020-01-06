#ifndef _SYMBOL_HPP__
#define _SYMBOL_HPP__

#include <cstdlib>
#include <iostream>

namespace flg {

enum class Symbol {
  boxed_i32,
  boxed_i64,
  boxed_fp32,
  boxed_fp64,
  boxed_string,
/* INSERT 0 */
};

std::ostream& operator<<(std::ostream& out, const Symbol& sym) {
	switch (sym) {
	  case Symbol::boxed_i32: return out << "boxed_i32";
	  case Symbol::boxed_i64: return out << "boxed_i64";
	  case Symbol::boxed_fp32: return out << "boxed_fp32";
	  case Symbol::boxed_fp64: return out << "boxed_fp64";
	  case Symbol::boxed_string: return out << "boxed_string";
/* INSERT 1 */
	}
}

} // namespace flg

#endif
