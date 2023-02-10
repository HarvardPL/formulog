#pragma once

#include <atomic>
#include <cassert>
#include <cstdlib>
#include <map>
#include <utility>
#include <vector>

#include "Symbol.hpp"

namespace flg {

struct Type;
struct TypeSubst;

typedef std::pair<std::vector<Type>, Type> functor_type;

struct Type {
    string name;
    bool is_var;
    std::vector<Type> args;

    static functor_type lookup(Symbol sym);

    static functor_type i32;
    static functor_type i64;
    static functor_type fp32;
    static functor_type fp64;
    static functor_type string_;
    static functor_type bool_;
    static functor_type model;

private:
    static functor_type make_prim(const std::string &name);

    static functor_type make_prim(const std::string &name, const std::vector<Type> &args);

    static Type make_index(const std::string &name);

    static Type new_var();

    static std::atomic_size_t cnt;
};

inline bool operator<(const Type &lhs, const Type &rhs) {
    return lhs.name < rhs.name;
}

struct TypeSubst {
    void put(const Type &var, const Type &other);

    Type apply(const Type &type);

    void clear();

private:
    std::map<Type, Type> m;
};

ostream &operator<<(ostream &out, const Type &type);

} // namespace flg
