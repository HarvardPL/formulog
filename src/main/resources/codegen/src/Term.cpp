#include <array>
#include <limits>
#include <stack>
#include <type_traits>
#include <utility>

#include "Term.hpp"

namespace flg {

template <typename T>
int BaseTerm<T>::compare(const BaseTerm<T>& t1, const BaseTerm<T>& t2) {
  return (t1.val > t2.val) - (t1.val < t2.val);
}

// Specializations for BaseTerm<float> and BaseTerm<double>
// This creates a total order where NaNs compare after everything else, avoiding
// undefined behavior when calling std::sort() in natural order.

template <>
int BaseTerm<float>::compare(
  const BaseTerm<float>& t1, const BaseTerm<float>& t2
) {
  if (isunordered(t1.val, t2.val)) {
    return isnan(t1.val) - isnan(t2.val);
  }
  return (t1.val > t2.val) - (t1.val < t2.val);
}

template <>
int BaseTerm<double>::compare(
  const BaseTerm<double>& t1, const BaseTerm<double>& t2
) {
  if (isunordered(t1.val, t2.val)) {
    return isnan(t1.val) - isnan(t2.val);
  }
  return (t1.val > t2.val) - (t1.val < t2.val);
}

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

// Template hash function for arrays of term_ptr's
template <size_t N>
struct ComplexTermHash {
  typedef array<term_ptr, N> key_type;

  size_t operator()(const key_type& arr) const {
    size_t retval = 0;
    for (term_ptr p : arr) {
      retval ^=
        (retval << 32) + 0xdeadbeef + reinterpret_cast<size_t>(p) / sizeof(p);
    }
    return retval;
  }
};

// Concurrency-safe cache for ComplexTerm values
template <Symbol S> class ComplexTermCache {
  inline static constexpr size_t arity = symbol_arity(S);
  typedef concurrent_unordered_map<
    array<term_ptr, arity>, term_ptr, ComplexTermHash<arity>> map_t;
  inline static map_t cache;

  public:
  template <typename... T,
            typename = enable_if_t<sizeof...(T) == arity>>
  static term_ptr get(T... val) {
    array<term_ptr, arity> arr = { val... };
    auto it = cache.find(arr);
    if (it != cache.end()) {
      return it->second;
    }
    term_ptr* heap_arr = new term_ptr[arity] { val... };
    auto ptr = new ComplexTerm(S, arity, heap_arr);
    auto result = cache.insert({arr, ptr});
    if (!result.second) {
      // Term was not successfully inserted
      delete ptr;
    }
    return result.first->second;
  }
};

template <Symbol S, typename... T>
term_ptr Term::make(T... val) {
  return ComplexTermCache<S>::get(val...);
}

/* INSERT 0 */

}
