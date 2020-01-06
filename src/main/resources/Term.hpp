#ifndef _TERM_HPP__
#define _TERM_HPP__

#include <cstdint>
#include <algorithm>
#include <memory>
#include <stack>
#include <utility>
#include "Symbol.hpp"

namespace flg {

struct Term {
  Symbol sym;

  static int compare(const Term* t1, const Term* t2);
};

struct ComplexTerm : public Term {
  size_t arity;
  std::shared_ptr<Term>* val;

  ComplexTerm(Symbol sym_, size_t arity_, std::shared_ptr<Term>* val_) :
    Term{sym_}, arity{arity_}, val{val_} {}

  ComplexTerm(const ComplexTerm& t) :
    Term{t.sym}, arity{t.arity}, val{new std::shared_ptr<Term>[t.arity]} {
    std::copy(t.val, t.val + t.arity, val);
  }

  ComplexTerm& operator=(const ComplexTerm& t) {
    if (this != &t) {
      std::shared_ptr<Term>* new_val = new std::shared_ptr<Term>[t.arity];
      std::copy(t.val, t.val + t.arity, new_val);
      delete[] val;
      sym = t.sym;
      arity = t.arity;
      val = new_val;
    }
    return *this;
  }

  ~ComplexTerm() {
    delete[] val;
  }
};

template<typename T>
struct BaseTerm : public Term {
  T val;

  friend BaseTerm<int32_t> mk_i32(int32_t val);
  friend BaseTerm<int64_t> mk_i64(int64_t val);
  friend BaseTerm<float> mk_fp32(float val);
  friend BaseTerm<double> mk_fp64(double val);
  friend BaseTerm<std::string> mk_string(std::string val);

  inline static int compare(BaseTerm<T> t1, BaseTerm<T> t2) {
    if (t1.val < t2.val) {
      return -1;
    } else if (t1.val > t2.val) {
      return 1;
    } else {
      return 0;
    }
  }

private:
  BaseTerm(Symbol sym_, T val_) : Term{sym_}, val(val_) {}
};

BaseTerm<int32_t> mk_i32(int32_t val) {
  return BaseTerm<int32_t>(Symbol::boxed_i32, val);
}

BaseTerm<int64_t> mk_i64(int64_t val) {
  return BaseTerm<int64_t>(Symbol::boxed_i64, val);
}

BaseTerm<float> mk_fp32(float val) {
  return BaseTerm<float>(Symbol::boxed_fp32, val);
}

BaseTerm<double> mk_fp64(double val) {
  return BaseTerm<double>(Symbol::boxed_fp64, val);
}

BaseTerm<std::string> mk_string(std::string val) {
  return BaseTerm<std::string>(Symbol::boxed_string, val);
}

int Term::compare(const Term* t1, const Term* t2) {
  std::stack<std::pair<const Term*, const Term*>> w;
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
      case Symbol::boxed_i32: {
        auto x = reinterpret_cast<const BaseTerm<int32_t>*>(t1);
        auto y = reinterpret_cast<const BaseTerm<int32_t>*>(t2);
        int cmp = BaseTerm<int32_t>::compare(*x, *y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i64: {
        auto x = reinterpret_cast<const BaseTerm<int64_t>*>(t1);
        auto y = reinterpret_cast<const BaseTerm<int64_t>*>(t2);
        int cmp = BaseTerm<int64_t>::compare(*x, *y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp32: {
        auto x = reinterpret_cast<const BaseTerm<float>*>(t1);
        auto y = reinterpret_cast<const BaseTerm<float>*>(t2);
        int cmp = BaseTerm<float>::compare(*x, *y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp64: {
        auto x = reinterpret_cast<const BaseTerm<double>*>(t1);
        auto y = reinterpret_cast<const BaseTerm<double>*>(t2);
        int cmp = BaseTerm<double>::compare(*x, *y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_string: {
        auto x = reinterpret_cast<const BaseTerm<std::string>*>(t1);
        auto y = reinterpret_cast<const BaseTerm<std::string>*>(t2);
        int cmp = BaseTerm<std::string>::compare(*x, *y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      default: {
        auto x = reinterpret_cast<const ComplexTerm*>(t1);
        auto y = reinterpret_cast<const ComplexTerm*>(t2);
        size_t n = x->arity;
        for (size_t i = 0; i < n; ++i) {
          w.emplace(x->val[i].get(), y->val[i].get()); 
        }
      }
    }
  }
  return 0;
}

} // namespace flg

#endif
