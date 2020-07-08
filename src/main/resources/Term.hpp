#pragma once

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <limits>
#include <memory>
#include <stack>
#include <utility>
#include <vector>

#include "Symbol.hpp"

namespace flg {

using namespace std;

struct Term;

typedef Term* term_ptr;

template <typename T> struct BaseTerm;
struct ComplexTerm;

struct Term {
  const Symbol sym;

  Term(Symbol sym_) : sym{sym_} {}

  template<typename T> inline const BaseTerm<T>& as_base() const;
  inline const ComplexTerm& as_complex() const;

  static int compare(Term* t1, Term* t2);
  template<typename T> inline static term_ptr make(T val);
  inline static term_ptr make(Symbol sym, size_t arity, term_ptr* val);
  static vector<term_ptr> vectorizeListTerm(Term* t);
};

struct ComplexTerm : public Term {
  const size_t arity;
  const term_ptr* const val;

  ComplexTerm(Symbol sym_, size_t arity_, term_ptr* val_) :
    Term{sym_}, arity{arity_}, val{val_} {}

  ~ComplexTerm() {
    delete[] val;
  }
};

template<typename T>
struct BaseTerm : public Term {
  const T val;

  BaseTerm(Symbol sym_, T val_) : Term{sym_}, val(val_) {}

  inline static int compare(BaseTerm<T> t1, BaseTerm<T> t2) {
    if (t1.val < t2.val) {
      return -1;
    } else if (t1.val > t2.val) {
      return 1;
    } else {
      return 0;
    }
  }
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
      auto x = t.as_complex();
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
        auto x = t1->as_base<bool>();
        auto y = t2->as_base<bool>();
        int cmp = BaseTerm<bool>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i32: {
        auto x = t1->as_base<int32_t>();
        auto y = t2->as_base<int32_t>();
        int cmp = BaseTerm<int32_t>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i64: {
        auto x = t1->as_base<int64_t>();
        auto y = t2->as_base<int64_t>();
        int cmp = BaseTerm<int64_t>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp32: {
        auto x = t1->as_base<float>();
        auto y = t2->as_base<float>();
        int cmp = BaseTerm<float>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp64: {
        auto x = t1->as_base<double>();
        auto y = t2->as_base<double>();
        int cmp = BaseTerm<double>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_string: {
        auto x = t1->as_base<string>();
        auto y = t2->as_base<string>();
        int cmp = BaseTerm<string>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      default: {
        auto x = t1->as_complex();
        auto y = t2->as_complex();
        size_t n = x.arity;
        for (size_t i = 0; i < n; ++i) {
          w.emplace(x.val[i], y.val[i]); 
        }
      }
    }
  }
  return 0;
}

term_ptr min_term = new Term(Symbol::min_term);
term_ptr max_term = new Term(Symbol::max_term);

template<>
term_ptr Term::make<bool>(bool val) {
  return new BaseTerm<bool>(Symbol::boxed_bool, val);
}

template<>
term_ptr Term::make<int32_t>(int32_t val) {
  return new BaseTerm<int32_t>(Symbol::boxed_i32, val);
}

template<>
term_ptr Term::make<int64_t>(int64_t val) {
  return new BaseTerm<int64_t>(Symbol::boxed_i64, val);
}

template<>
term_ptr Term::make<float>(float val) {
  return new BaseTerm<float>(Symbol::boxed_fp32, val);
}

template<>
term_ptr Term::make<double>(double val) {
  return new BaseTerm<double>(Symbol::boxed_fp64, val);
}

template<>
term_ptr Term::make<string>(string val) {
  return new BaseTerm<string>(Symbol::boxed_string, val);
}

term_ptr Term::make(Symbol sym, size_t arity, term_ptr* val) {
  return new ComplexTerm(sym, arity, val);
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

vector<term_ptr> Term::vectorizeListTerm(Term* t) {
  vector<term_ptr> v;
  while (t->sym == Symbol::cons) {
    auto x = t->as_complex();
    v.push_back(x.val[0]);
    t = x.val[1];
  }
  assert(t->sym == Symbol::nil);
  return v;
}

} // namespace flg
