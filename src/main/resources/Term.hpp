#pragma once

#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <shared_mutex>
#include <stack>
#include <type_traits>
#include <utility>
#include <vector>

#include "Symbol.hpp"

#define NO_COPY_OR_ASSIGN(t) \
  t(const t&) = delete; t(t&&) = delete; \
  t& operator=(const t&) = delete; \
  t& operator=(t&&) = delete;

namespace flg {

using namespace std;

struct Term;

typedef Term* term_ptr;

template <typename T> struct BaseTerm;
struct ComplexTerm;

template <typename T, Symbol S> class BaseTermCache;
template <Symbol S> class ComplexTermCache;

struct Term {
  const Symbol sym;

  NO_COPY_OR_ASSIGN(Term);

  template<typename T> inline const BaseTerm<T>& as_base() const;
  inline const ComplexTerm& as_complex() const;

  // Compare two terms by their memory address -> {-1, 0, 1}
  static int compare(Term* t1, Term* t2);

  // Compare two terms by their natural order -> {-1, 0, 1}:
  // - if of the different types, then by order in the Symbol enum
  // - if of the same type BaseTerm<T>, then by T::operator<()
  // - if of the same type ComplexTerm, then by lexicographical order
  static int compare_natural(Term* t1, Term* t2);

  // Construct a memoized BaseTerm
  template <typename T>
  inline static term_ptr make(T val);

  // Construct a memoized ComplexTerm
  template <Symbol S, typename... T>
  inline static term_ptr make(T... val);

  // Convert a Lisp-style list term into a vector
  static vector<term_ptr> vectorize_list_term(Term* t);

  protected:
  Term(Symbol sym_) : sym{sym_} {}
};

struct ComplexTerm : public Term {
  const size_t arity;
  const term_ptr* const val;

  NO_COPY_OR_ASSIGN(ComplexTerm);

  private:
  ComplexTerm(Symbol sym_, size_t arity_, term_ptr* val_) :
    Term{sym_}, arity{arity_}, val{val_} {}

  ~ComplexTerm() {
    delete[] val;
  }

  template <Symbol> friend class ComplexTermCache;
};

template<typename T>
struct BaseTerm : public Term {
  const T val;

  NO_COPY_OR_ASSIGN(BaseTerm);

  inline static int compare(const BaseTerm<T>& t1, const BaseTerm<T>& t2) {
    return (t1.val > t2.val) - (t1.val < t2.val);
  }

  private:
  BaseTerm(Symbol sym_, T val_) : Term{sym_}, val(val_) {}

  template <typename, Symbol> friend class BaseTermCache;
};

ostream& operator<<(ostream& out, Term& t) {
  switch (t.sym) {
    case Symbol::boxed_bool: {
      return out << boolalpha << t.as_base<bool>().val << noboolalpha;
    }
    case Symbol::boxed_i32: {
      return out << t.as_base<int32_t>().val;
    }
    case Symbol::boxed_i64: {
      return out << t.as_base<int64_t>().val << "L";
    }
    case Symbol::boxed_fp32: {
      auto val = t.as_base<float>().val;
      if (isnan(val)) {
        out << "fp32_nan";
      } else if (isinf(val)) {
        if (val > 0) {
          out << "fp32_pos_infinity";
        } else {
          out << "fp32_neg_infinity";
        }
      } else {
        out << val << "F";
      }
      return out;
    }
    case Symbol::boxed_fp64: {
      auto val = t.as_base<double>().val;
      if (isnan(val)) {
        out << "fp64_nan";
      } else if (isinf(val)) {
        if (val > 0) {
          out << "fp64_pos_infinity";
        } else {
          out << "fp64_neg_infinity";
        }
      } else {
        out << val << "F";
      }
      return out;
    }
    case Symbol::boxed_string: {
      return out << "\"" << t.as_base<string>().val << "\"";
    }
    default: {
      auto& x = t.as_complex();
      out << x.sym;
      size_t n = x.arity;
      if (n > 0) {
        out << "(";
        for (size_t i = 0; i < n; ++i) {
          out << *x.val[i];
          if (i < n - 1) {
            out << ", ";
          }
        }
        out << ")";
      }
      return out;
    }
  }
}

int Term::compare(Term* t1, Term* t2) {
  return less<>()(t2, t1) - less<>()(t1, t2);
}

int Term::compare_natural(Term* t1, Term* t2) {
  stack<pair<Term*, Term*>> w;
  w.emplace(t1, t2);
  while (!w.empty()) {
    auto p = w.top();
    w.pop();
    t1 = p.first;
    t2 = p.second;
    if (t1 == t2) {
      continue;
    }
    if (t1->sym < t2->sym) {
      return -1;
    }
    if (t1->sym > t2->sym) {
      return 1;
    }
    switch (t1->sym) {
      case Symbol::boxed_bool: {
        auto& x = t1->as_base<bool>();
        auto& y = t2->as_base<bool>();
        int cmp = BaseTerm<bool>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i32: {
        auto& x = t1->as_base<int32_t>();
        auto& y = t2->as_base<int32_t>();
        int cmp = BaseTerm<int32_t>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i64: {
        auto& x = t1->as_base<int64_t>();
        auto& y = t2->as_base<int64_t>();
        int cmp = BaseTerm<int64_t>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp32: {
        auto& x = t1->as_base<float>();
        auto& y = t2->as_base<float>();
        int cmp = BaseTerm<float>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp64: {
        auto& x = t1->as_base<double>();
        auto& y = t2->as_base<double>();
        int cmp = BaseTerm<double>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_string: {
        auto& x = t1->as_base<string>();
        auto& y = t2->as_base<string>();
        int cmp = BaseTerm<string>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      default: {
        auto& x = t1->as_complex();
        auto& y = t2->as_complex();
        size_t n = x.arity;
        for (size_t i = 0; i < n; ++i) {
          w.emplace(x.val[i], y.val[i]); 
        }
      }
    }
  }
  return 0;
}

// These terms do not exist, but are useful for pointer comparisons
term_ptr min_term = reinterpret_cast<term_ptr>(numeric_limits<uintptr_t>::min());
term_ptr max_term = reinterpret_cast<term_ptr>(numeric_limits<uintptr_t>::max());

// Concurrency-safe cache for BaseTerm values
template <typename T, Symbol S> class BaseTermCache {
  inline static unordered_map<T, term_ptr> cache;
  inline static shared_mutex m;

  public:
  static term_ptr get(const T& val) {
    shared_lock<shared_mutex> lock(m);
    auto it = cache.find(val);
    if (it != cache.end()) {
      return it->second;
    }
    lock.unlock();
    unique_lock<shared_mutex> lock2(m);
    return cache[val] = new BaseTerm<T>(S, val);
  }
};

template<>
term_ptr Term::make<bool>(bool val) {
  return BaseTermCache<bool, Symbol::boxed_bool>::get(val);
}

template<>
term_ptr Term::make<int32_t>(int32_t val) {
  return BaseTermCache<int32_t, Symbol::boxed_i32>::get(val);
}

template<>
term_ptr Term::make<int64_t>(int64_t val) {
  return BaseTermCache<int64_t, Symbol::boxed_i64>::get(val);
}

template<>
term_ptr Term::make<float>(float val) {
  return BaseTermCache<float, Symbol::boxed_fp32>::get(val);
}

template<>
term_ptr Term::make<double>(double val) {
  return BaseTermCache<double, Symbol::boxed_fp64>::get(val);
}

template<>
term_ptr Term::make<string>(string val) {
  return BaseTermCache<string, Symbol::boxed_string>::get(val);
}

// Template hash function for arrays of term_ptr's
template <size_t N>
struct ComplexTermHash {
  size_t operator()(const array<term_ptr, N>& arr) const {
    size_t retval = 0;
    for (term_ptr p : arr) {
      retval ^= (retval << 32) + 0xdeadbeef + reinterpret_cast<size_t>(p);
    }
    return retval;
  }
};

// Concurrency-safe cache for ComplexTerm values
template <Symbol S> class ComplexTermCache {
  static constexpr size_t arity = symbol_arity(S);
  inline static unordered_map<array<term_ptr, arity>, term_ptr, ComplexTermHash<arity>> cache;
  inline static shared_mutex m;

  public:
  template <typename... T,
            typename = enable_if_t<sizeof...(T) == arity>>
  inline static term_ptr get(T... val) {
    array<term_ptr, arity> arr = { val... };
    shared_lock<shared_mutex> lock(m);
    auto it = cache.find(arr);
    if (it != cache.end()) {
      return it->second;
    }
    lock.unlock();
    term_ptr* heap_arr = new term_ptr[arity] { val... };
    unique_lock<shared_mutex> lock2(m);
    return cache[arr] = new ComplexTerm(S, arity, heap_arr);
  }
};

template <Symbol S, typename... T>
term_ptr Term::make(T... val) {
  return ComplexTermCache<S>::get(val...);
}

template<typename T>
const BaseTerm<T>& Term::as_base() const {
  return reinterpret_cast<const BaseTerm<T>&>(*this);
}

const ComplexTerm& Term::as_complex() const {
  return reinterpret_cast<const ComplexTerm&>(*this);
}

struct TermCompare {
  bool operator()(Term* lhs, Term* rhs) const {
    return Term::compare(lhs, rhs) < 0;
  }
};

vector<term_ptr> Term::vectorize_list_term(Term* t) {
  vector<term_ptr> v;
  while (t->sym == Symbol::cons) {
    auto& x = t->as_complex();
    v.push_back(x.val[0]);
    t = x.val[1];
  }
  assert(t->sym == Symbol::nil);
  return v;
}

} // namespace flg
