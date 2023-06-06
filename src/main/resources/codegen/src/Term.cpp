#include <array>
#include <stack>
#include <type_traits>
#include <utility>

#include "Term.hpp"

namespace flg {

ostream &operator<<(ostream &out, const Term &t) {
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

// Concurrency-safe cache for ComplexTerm values
template <Symbol S> class ComplexTermCache {
  inline static constexpr size_t arity = symbol_arity(S);
  typedef array<term_ptr, arity> key_t;
  typedef ConcurrentHashMap<key_t, term_ptr, boost::hash<key_t>> map_t;
  inline static map_t cache;

  public:
  template <typename... T,
            typename = enable_if_t<sizeof...(T) == arity>>
  static term_ptr get(T... val) {
      array<term_ptr, arity> arr = {val...};
      auto it = cache.find(arr);
      if (it != cache.end()) {
          return it->second;
      }
      auto *heap_arr = new term_ptr[arity]{val...};
      auto ptr = new ComplexTerm(S, arity, heap_arr);
      auto result = cache.emplace(arr, ptr);
      if (!result.second) {
          // Term was not successfully inserted
          delete ptr;
      }
      return result.first->second;
  }
};

template<Symbol S, typename... T>
term_ptr Term::make(T... val) {
    return ComplexTermCache<S>::get(val...);
}

/* INSERT 0 */

term_ptr ComplexTerm::fresh_smt_var() {
#ifdef FLG_DEV
    return nullptr;
#else
    return new ComplexTerm(Symbol::smt_var__bool__bool, 0, nullptr);
#endif
}

term_ptr Term::make_generic(Symbol sym, const vector<term_ptr> &terms) {
    if (symbol_arity(sym) != terms.size()) {
        string message = "Expected arity ";
        message += to_string(symbol_arity(sym));
        message += " for symbol (ID ";
        message += to_string(static_cast<int>(sym));
        message += "), got arity ";
        message += to_string(terms.size());
        throw std::runtime_error(message);
    }
    switch (sym) {
/* INSERT 1 */
        default:
            throw std::runtime_error(
                    "Invalid symbol (ID " +
                    to_string(static_cast<int>(sym)) +
                    ") used to construct term"
            );
    }
}


}
