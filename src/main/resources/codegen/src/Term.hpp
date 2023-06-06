#pragma once

#include <cassert>
#include <cmath>
#include <cstdint>
#include <vector>

#include <boost/container_hash/hash.hpp>
#include <souffle/SouffleInterface.h>

#include "set.hpp"
#include "ConcurrentHashMap.hpp"
#include "Symbol.hpp"

#define NO_COPY_OR_ASSIGN(t) \
  t(const t&) = delete; t(t&&) = delete; \
  t& operator=(const t&) = delete; \
  t& operator=(t&&) = delete;

namespace flg {

using namespace std;

struct Term;

typedef const Term *term_ptr;

template<typename T>
struct BaseTerm;
struct ComplexTerm;

template<typename T, Symbol S>
class BaseTermCache;

template<Symbol S>
class ComplexTermCache;

struct Term {
    const Symbol sym;

    NO_COPY_OR_ASSIGN(Term);

    template<typename T>
    [[nodiscard]] inline const BaseTerm<T> &as_base() const;

    [[nodiscard]] inline const ComplexTerm &as_complex() const;

    // Construct a memoized BaseTerm
    template<typename T>
    inline static term_ptr make(T val);

    template<typename T>
    inline static term_ptr make_moved(T &&val);

    // Construct a memoized ComplexTerm
    template<Symbol S, typename... T>
    static term_ptr make(T... val);

    // Convert a Lisp-style list term into a vector
    inline static vector<term_ptr> vectorize_list_term(term_ptr t);

    [[nodiscard]] souffle::RamDomain intize() const {
        return (souffle::RamDomain) (uintptr_t) (void *) this;
    }

    static term_ptr unintize(souffle::RamDomain id) {
        return (term_ptr) (void *) (uintptr_t) id;
    }

    static term_ptr make_generic(Symbol sym, const vector<term_ptr> &terms);

protected:
    explicit Term(Symbol sym_) : sym{sym_} {}
};

struct ComplexTerm : public Term {
    const size_t arity;
    const term_ptr *const val;

    NO_COPY_OR_ASSIGN(ComplexTerm);

    static term_ptr fresh_smt_var();

private:
    ComplexTerm(Symbol sym_, size_t arity_, term_ptr *val_) :
            Term{sym_}, arity{arity_}, val{val_} {}

    ~ComplexTerm() {
        delete[] val;
    }

    template<Symbol> friend
    class ComplexTermCache;
};

template<typename T>
struct BaseTerm : public Term {
    const T val;

    NO_COPY_OR_ASSIGN(BaseTerm);

private:
    BaseTerm(Symbol sym_, T &&val_) : Term{sym_}, val{std::move(val_)} {}

    template<typename, Symbol> friend
    class BaseTermCache;
};

ostream &operator<<(ostream &out, const Term &t);

// Concurrency-safe cache for BaseTerm values
template<typename T, Symbol S>
class BaseTermCache {
    struct Hash {
        std::size_t operator()(const T *const &val) const {
            return boost::hash<T>{}(*val);
        }
    };

    struct Equals {
        bool operator()(const T *const &val1, const T *const &val2) const {
            return *val1 == *val2;
        }
    };

    typedef ConcurrentHashMap<const T*, term_ptr, Hash, Equals> map_t;
    inline static map_t cache;

public:
    static term_ptr get(T &&val) {
        auto it = cache.find(&val);
        if (it != cache.end()) {
            return it->second;
        }
        auto ptr = new BaseTerm<T>(S, std::move(val));
        auto result = cache.emplace(&ptr->val, ptr);
        if (!result.second) {
            // Term was not successfully inserted
            delete ptr;
        }
        return result.first->second;
    }
};

template<>
inline term_ptr Term::make<bool>(bool val) {
    typedef BaseTermCache<bool, Symbol::boxed_bool> cache;
    // Optimization to avoid unnecessary lock contention
    static const term_ptr true_term = cache::get(true);
    static const term_ptr false_term = cache::get(false);
    return val ? true_term : false_term;
}

template<>
inline term_ptr Term::make<int32_t>(int32_t val) {
    return BaseTermCache<int32_t, Symbol::boxed_i32>::get(std::move(val));
}

template<>
inline term_ptr Term::make<int64_t>(int64_t val) {
    return BaseTermCache<int64_t, Symbol::boxed_i64>::get(std::move(val));
}

template<>
inline term_ptr Term::make<float>(float val) {
    typedef BaseTermCache<float, Symbol::boxed_fp32> cache;
    // NaN is a special case due to ill-behaved floating point comparison
    static const term_ptr nan32_term = cache::get(nanf(""));
    if (isnan(val)) {
        return nan32_term;
    }
    return cache::get(std::move(val));
}

template<>
inline term_ptr Term::make<double>(double val) {
    typedef BaseTermCache<double, Symbol::boxed_fp64> cache;
    // NaN is a special case due to ill-behaved floating point comparison
    static const term_ptr nan64_term = cache::get(nan(""));
    if (isnan(val)) {
        return nan64_term;
    }
    return cache::get(std::move(val));
}

template<>
inline term_ptr Term::make<string>(string val) {
    return BaseTermCache<string, Symbol::boxed_string>::get(std::move(val));
}

template<>
inline term_ptr Term::make_moved<string>(string &&val) {
    return BaseTermCache<string, Symbol::boxed_string>::get(std::move(val));
}

typedef std::map<term_ptr, term_ptr> Model;

template<>
inline term_ptr Term::make_moved<Model>(Model &&val) {
    return BaseTermCache<Model, Symbol::model>::get(std::move(val));
}

template<>
inline term_ptr Term::make_moved(Set &&val) {
    return BaseTermCache<Set, Symbol::opaque_set>::get(std::move(val));
}

template<typename T>
const BaseTerm<T> &Term::as_base() const {
    return reinterpret_cast<const BaseTerm<T> &>(*this);
}

const ComplexTerm &Term::as_complex() const {
    return reinterpret_cast<const ComplexTerm &>(*this);
}

inline vector<term_ptr> Term::vectorize_list_term(term_ptr t) {
    vector<term_ptr> v;
#ifndef FLG_DEV
    while (t->sym == Symbol::cons) {
      auto& x = t->as_complex();
      v.push_back(x.val[0]);
      t = x.val[1];
    }
    assert(t->sym == Symbol::nil);
#endif
    return v;
}

} // namespace flg
