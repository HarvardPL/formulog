//
// Created by Aaron Bembenek on 8/10/22.
//

#include "Type.hpp"

namespace flg {

void TypeSubst::put(const Type &var, const Type &other) {
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

Type TypeSubst::apply(const Type &ty) {
    if (ty.is_var) {
        auto v = m.find(ty);
        if (v == m.end()) {
            return ty;
        } else {
            return apply(v->second);
        }
    }
    std::vector<Type> newArgs;
    for (auto &arg: ty.args) {
        newArgs.push_back(apply(arg));
    }
    return Type{ty.name, ty.is_var, newArgs};
}

void TypeSubst::clear() {
    m.clear();
}

std::ostream &operator<<(std::ostream &out, const Type &type) {
    auto args = type.args;
    if (!args.empty()) {
        out << "(";
    }
    out << type.name;
    for (auto &arg: args) {
        out << " " << arg;
    }
    if (!args.empty()) {
        out << ")";
    }
    return out;
}

functor_type Type::make_prim(const std::string &name, const std::vector<Type> &args) {
    return make_pair(std::vector<Type>(), Type{name, false, args});
}

functor_type Type::make_prim(const std::string &name) {
    return make_prim(name, {});
}

Type Type::make_index(const std::string &name) {
    return Type{name, false, {}};
}

functor_type Type::bool_ = make_prim("Bool");
functor_type Type::i32 = make_prim("_ BitVec", {make_index("32")});
functor_type Type::i64 = make_prim("_ BitVec", {make_index("64")});
functor_type Type::fp32 = make_prim("_ FloatingPoint", {make_index("8"), make_index("24")});
functor_type Type::fp64 = make_prim("_ FloatingPoint", {make_index("11"), make_index("53")});
functor_type Type::string_ = make_prim("String");
functor_type Type::model = make_prim("Model");

atomic_size_t Type::cnt;

Type Type::new_var() {
    return Type{"x" + to_string(cnt++), true, {}};
}

functor_type Type::lookup(Symbol sym) {
    switch (sym) {
        case Symbol::boxed_bool:
            return bool_;
        case Symbol::boxed_i32:
            return i32;
        case Symbol::boxed_i64:
            return i64;
        case Symbol::boxed_fp32:
            return fp32;
        case Symbol::boxed_fp64:
            return fp64;
        case Symbol::boxed_string:
            return string_;
        case Symbol::model:
            return model;
/* INSERT 0 */
    }
    __builtin_unreachable();
}

}