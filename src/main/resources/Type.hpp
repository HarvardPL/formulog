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

  static functor_type lookup(Symbol sym); 

  static functor_type i32;
  static functor_type i64;
  static functor_type fp32;
  static functor_type fp64;
  static functor_type string_;
  static functor_type bool_;

  private:
  static functor_type make_prim(const string& name);
  static functor_type make_prim(const string& name, const vector<Type>& args);
  static Type make_index(const string& name);
  static Type new_var();
  static atomic_size_t cnt;
};

inline bool operator<(const Type& lhs, const Type& rhs) {
  return lhs.name < rhs.name;
}

struct TypeSubst {
  void put(const Type var, const Type other);
  Type apply(const Type& type);
  void clear();

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
  for (auto& arg : ty.args) {
    newArgs.push_back(apply(arg));
  }
  return Type{ty.name, ty.is_var, newArgs};
}

void TypeSubst::clear() {
  m.clear();
}

ostream& operator<<(ostream& out, const Type& type) {
  auto args = type.args;
  if (!args.empty()) {
    out << "(";
  }
  out << type.name;
  for (auto& arg : args) {
    out << " " << arg;
  }
  if (!args.empty()) {
    out << ")";
  }
  return out;
}

functor_type Type::make_prim(const string& name, const vector<Type>& args) {
  return make_pair(vector<Type>(), Type{name, false, args});
}

functor_type Type::make_prim(const string& name) {
  return make_prim(name, {});
}

Type Type::make_index(const string& name) {
  return Type{name, false, {}};
}

functor_type Type::bool_ = make_prim("Bool");
functor_type Type::i32 = make_prim("_ BitVec", { make_index("32") });
functor_type Type::i64 = make_prim("_ BitVec", { make_index("64") });
functor_type Type::fp32 = make_prim("_ FloatingPoint", { make_index("8"), make_index("24") });
functor_type Type::fp64 = make_prim("_ FloatingPoint", { make_index("11"), make_index("53") });
functor_type Type::string_ = make_prim("String"); 

atomic_size_t Type::cnt;

Type Type::new_var() {
  return Type{"x" + to_string(cnt++), true, {}};
}

functor_type Type::lookup(Symbol sym) {
  switch (sym) {
    case Symbol::boxed_bool: return bool_;
    case Symbol::boxed_i32: return i32;
    case Symbol::boxed_i64: return i64;
    case Symbol::boxed_fp32: return fp32;
    case Symbol::boxed_fp64: return fp64;
    case Symbol::boxed_string: return string_;
/* INSERT 0 */
  }
  __builtin_unreachable();
}

} // namespace flg
