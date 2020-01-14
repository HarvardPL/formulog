#ifndef FUNCTIONS_HPP__
#define FUNCTIONS_HPP__

#include <algorithm>
#include <sstream>
#include <regex>

#include "Term.hpp"

namespace flg {

namespace funcs {

using namespace std;

term_ptr beq(const term_ptr& t1, const term_ptr& t2) {
  return Term::make<bool>(!Term::compare(t1.get(), t2.get()));
}

term_ptr bneq(const term_ptr& t1, const term_ptr& t2) {
  return Term::make<bool>(Term::compare(t1.get(), t2.get()));
}

term_ptr bnot(const term_ptr& t1) {
  auto x = reinterpret_cast<BaseTerm<bool>*>(t1.get());
  return Term::make<bool>(!x->val);
}

template <typename T>
term_ptr __add(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val + y->val);
}

template <typename T>
term_ptr __sub(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val - y->val);
}

template <typename T>
term_ptr __mul(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val * y->val);
}

template <typename T>
term_ptr __div(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val / y->val);
}

template <typename T>
term_ptr __rem(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val % y->val);
}

template <typename T>
term_ptr __bitwise_and(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val & y->val);
}

template <typename T>
term_ptr __bitwise_or(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val | y->val);
}

template <typename T>
term_ptr __bitwise_xor(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val ^ y->val);
}

template <typename T>
term_ptr __neg(const term_ptr& t1) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  return Term::make(-x->val);
}

template <typename T>
term_ptr __eq(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make<bool>(x->val == y->val);
}

template <typename T>
term_ptr __lt(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val < y->val);
}

template <typename T>
term_ptr __le(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val <= y->val);
}

template <typename T>
term_ptr __gt(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val > y->val);
}

template <typename T>
term_ptr __ge(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val >= y->val);
}

template <typename T>
term_ptr __cmp(const term_ptr& t1, const term_ptr& t2) {
  auto xval = reinterpret_cast<BaseTerm<T>*>(t1.get())->val;
  auto yval = reinterpret_cast<BaseTerm<T>*>(t2.get())->val;
  Symbol sym{Symbol::cmp_eq};
  if (xval < yval) {
    sym = Symbol::cmp_lt;
  } else if (xval > yval) {
    sym = Symbol::cmp_gt;
  }
  return Term::make(sym, 0, new term_ptr[0]);
}

term_ptr print(const term_ptr& t1) {
  cout << *t1 << endl;
  return Term::make<bool>(true);
}

term_ptr string_concat(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<string>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<string>*>(t2.get());
  return Term::make(x->val + y->val);
}

term_ptr string_matches(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<string>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<string>*>(t2.get());
  regex re(y->val);
  return Term::make<bool>(regex_match(x->val, re));
}

term_ptr string_starts_with(const term_ptr& t1, const term_ptr& t2) {
  auto str = reinterpret_cast<BaseTerm<string>*>(t1.get())->val;
  auto pre = reinterpret_cast<BaseTerm<string>*>(t2.get())->val;
  if (pre.size() > str.size()) {
    return Term::make<bool>(false);
  }
  auto res = mismatch(pre.begin(), pre.end(), str.begin());
  return Term::make<bool>(res.first == pre.end());
}

term_ptr to_string(const term_ptr& t1) {
  if (t1->sym == Symbol::boxed_string) {
    return t1;
  }
  stringstream ss;
  ss << *t1;
  return Term::make(ss.str());
}

template <typename S, typename T>
term_ptr __conv(const term_ptr& t1) {
  auto x = reinterpret_cast<BaseTerm<S>*>(t1.get());
  return Term::make<T>(x->val);
}
/* INSERT 0 */

} // namespace funcs
/* INSERT 1 */

} // namespace flg

#endif
