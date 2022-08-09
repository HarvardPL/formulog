#pragma once

#include <cassert>
#include <cmath>
#include <cstdint>
#include <vector>

#include <souffle/SouffleInterface.h>
#include <tbb/concurrent_unordered_map.h>

#include "Symbol.hpp"

#define NO_COPY_OR_ASSIGN(t) \
  t(const t&) = delete; t(t&&) = delete; \
  t& operator=(const t&) = delete; \
  t& operator=(t&&) = delete;

namespace flg {

using namespace std;
using tbb::concurrent_unordered_map;

struct Term;

typedef Term *term_ptr;
typedef const Term *const_term_ptr;

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
    inline const BaseTerm<T> &as_base() const;

    inline const ComplexTerm &as_complex() const;

    // Compare two terms by their memory address -> {-1, 0, 1}
    inline static int compare(Term *t1, Term *t2);

    // Compare two terms by their natural order -> {-1, 0, 1}:
    // - if of the different types, then by order in the Symbol enum
    // - if of the same type BaseTerm<T>, then by T::operator<()
    // - if of the same type ComplexTerm, then by lexicographical order
    static int compare_natural(Term *t1, Term *t2);

    // Construct a memoized BaseTerm
    template<typename T>
    inline static term_ptr make(T val);

    // Construct a memoized ComplexTerm
    template<Symbol S, typename... T>
    static term_ptr make(T... val);

    // Convert a Lisp-style list term into a vector
    inline static vector<term_ptr> vectorize_list_term(Term *t);

    [[nodiscard]] souffle::RamDomain intize() const {
        return (souffle::RamDomain) (uintptr_t) (void *) this;
        /*
        auto it = term_int_map.find(this);
        if (it != term_int_map.end()) {
            return it->second;
        }
        auto id = int_cnt++;
        auto result = term_int_map.emplace(this, id);
        if (!result.second) {
            return result.first->second;
        }
        auto result2 = int_term_map.emplace(id, this);
        assert(result2.second);
        return id;
         */
    }

    static term_ptr unintize(souffle::RamDomain id) {
        return (term_ptr) (void *) (uintptr_t) id;
        /*
        auto it = int_term_map.find(id);
        assert(it != int_term_map.end());
        return it->second;
         */
    }

    static term_ptr make_generic(Symbol sym, const vector<term_ptr> &terms);

protected:
    Term(Symbol sym_) : sym{sym_} {}

private:
    inline static concurrent_unordered_map<souffle::RamDomain, term_ptr> int_term_map;
    inline static concurrent_unordered_map<term_ptr, souffle::RamDomain> term_int_map;
    inline static std::atomic<souffle::RamDomain> int_cnt{0};
};

struct ComplexTerm : public Term {
    const size_t arity;
    const term_ptr *const val;

    NO_COPY_OR_ASSIGN(ComplexTerm);

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

    static int compare(const BaseTerm<T> &t1, const BaseTerm<T> &t2);

private:
    BaseTerm(Symbol sym_, T val_) : Term{sym_}, val(val_) {}

    template<typename, Symbol> friend
    class BaseTermCache;
};

ostream &operator<<(ostream &out, Term &t);

inline int Term::compare(Term *t1, Term *t2) {
    return less<>()(t2, t1) - less<>()(t1, t2);
}

// These terms do not exist, but are useful for pointer comparisons
inline const term_ptr min_term =
        reinterpret_cast<term_ptr>(numeric_limits<uintptr_t>::min());
inline const term_ptr max_term =
        reinterpret_cast<term_ptr>(numeric_limits<uintptr_t>::max());

// Concurrency-safe cache for BaseTerm values
template<typename T, Symbol S>
class BaseTermCache {
    typedef concurrent_unordered_map<T, term_ptr> map_t;
    inline static map_t cache;

public:
    static term_ptr get(const T &val) {
        auto it = cache.find(val);
        if (it != cache.end()) {
            return it->second;
        }
        auto ptr = new BaseTerm<T>(S, val);
        auto result = cache.insert({val, ptr});
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
    return BaseTermCache<int32_t, Symbol::boxed_i32>::get(val);
}

template<>
inline term_ptr Term::make<int64_t>(int64_t val) {
    return BaseTermCache<int64_t, Symbol::boxed_i64>::get(val);
}

template<>
inline term_ptr Term::make<float>(float val) {
    typedef BaseTermCache<float, Symbol::boxed_fp32> cache;
    // NaN is a special case due to ill-behaved floating point comparison
    static const term_ptr nan32_term = cache::get(nanf(""));
    if (isnan(val)) {
        return nan32_term;
    }
    return cache::get(val);
}

template<>
inline term_ptr Term::make<double>(double val) {
    typedef BaseTermCache<double, Symbol::boxed_fp64> cache;
    // NaN is a special case due to ill-behaved floating point comparison
    static const term_ptr nan64_term = cache::get(nan(""));
    if (isnan(val)) {
        return nan64_term;
    }
    return cache::get(val);
}

template<>
inline term_ptr Term::make<string>(string val) {
    return BaseTermCache<string, Symbol::boxed_string>::get(val);
}

template<typename T>
const BaseTerm<T> &Term::as_base() const {
    return reinterpret_cast<const BaseTerm<T> &>(*this);
}

const ComplexTerm &Term::as_complex() const {
    return reinterpret_cast<const ComplexTerm &>(*this);
}

struct TermCompare {
    inline bool operator()(Term *lhs, Term *rhs) const {
        return Term::compare(lhs, rhs) < 0;
    }
};

inline vector<term_ptr> Term::vectorize_list_term(Term *t) {
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
