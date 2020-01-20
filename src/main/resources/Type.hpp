#pragma once

#include <atomic>
#include <cstdlib>
#include <utility>
#include <vector>

#include "Symbol.hpp"

namespace flg {

using namespace std;

struct Type;

typedef pair<vector<Type>, Type> functor_type;

struct Type {
  string name;
  bool is_var;
  vector<Type> args;

  static functor_type lookup(const Symbol& sym); 

  private:
  static Type new_var();
  static atomic_size_t cnt;
};

ostream& operator<<(ostream& out, const Type& type) {
  auto args = type.args;
  if (!args.empty()) {
    out << "(";
  }
  out << type.name;
  for (auto it = args.begin(); it != args.end(); it++) {
    out << " ";
    out << *it;
  }
  if (!args.empty()) {
    out << ")";
  }
  return out;
}

functor_type bool_type = make_pair(vector<Type>(), Type{"Bool", false, {}});
functor_type i32_type = make_pair(vector<Type>(), Type{"(_ BitVec 32)", false, {}});
functor_type i64_type = make_pair(vector<Type>(), Type{"(_ BitVec 64)", false, {}});
functor_type fp32_type = make_pair(vector<Type>(), Type{"(_ FloatingPoint 8 24)", false, {}});
functor_type fp64_type = make_pair(vector<Type>(), Type{"(_ FloatingPoint 11 53)", false, {}});
functor_type string_type = make_pair(vector<Type>(), Type{"String", false, {}}); 

atomic_size_t Type::cnt;

Type Type::new_var() {
  return Type{"x" + cnt++, true, {}};
}

functor_type Type::lookup(const Symbol& sym) {
  switch (sym) {
    case Symbol::min_term:
    case Symbol::max_term:
      abort();
    case Symbol::boxed_bool: return bool_type;
    case Symbol::boxed_i32: return i32_type;
    case Symbol::boxed_i64: return i64_type;
    case Symbol::boxed_fp32: return fp32_type;
    case Symbol::boxed_fp64: return fp64_type;
    case Symbol::boxed_string: return string_type;
/* INSERT 0 */
  }
  __builtin_unreachable();
}

} // namespace flg
