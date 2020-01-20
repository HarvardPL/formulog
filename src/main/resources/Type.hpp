#pragma once

#include <atomic>
#include <cassert>
#include <cstdlib>
#include <map>
#include <utility>
#include <vector>

#include "Symbol.hpp"

namespace flg {

using namespace std;

struct Type;
struct TypeSubst;

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

inline bool operator<(const Type& lhs, const Type& rhs) {
  return lhs.name < rhs.name;
}

struct TypeSubst {
  void put(const Type var, const Type other);
  Type apply(const Type& type);

  private:
  map<Type, Type> m;
};

void TypeSubst::put(const Type var, const Type other) {
  assert(var.is_var);
  if (other.is_var) {
    if (var < other) {
      m.emplace(var, other);
    } else if (other < var) {
      m.emplace(other, var);
    }
  } else {
    m.emplace(var, other);
  }
}

Type TypeSubst::apply(const Type& ty) {
  if (ty.is_var) {
    auto v = m.find(ty);
    if (v == m.end()) {
      return ty;
    } else {
      return apply(v->second);
    }
  }
  vector<Type> newArgs;
  for (auto it = ty.args.begin(); it != ty.args.end(); it++) {
    newArgs.push_back(apply(*it));
  }
  return Type{ty.name, ty.is_var, newArgs};
}

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
