#pragma once

#include <algorithm>
#include <cstdlib>
#include <sstream>
#include <regex>

#include "Term.hpp"
#include "smt.hpp"
#include "rels.hpp"

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
  return Term::make<bool>(!t1->as_base<bool>().val);
}

template <typename T>
term_ptr __add(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val + t2->as_base<T>().val);
}

template <typename T>
term_ptr __sub(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val - t2->as_base<T>().val);
}

template <typename T>
term_ptr __mul(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val * t2->as_base<T>().val);
}

template <typename T>
term_ptr __div(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val / t2->as_base<T>().val);
}

template <typename T>
term_ptr __rem(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val % t2->as_base<T>().val);
}

template <typename T>
term_ptr __bitwise_and(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val & t2->as_base<T>().val);
}

template <typename T>
term_ptr __bitwise_or(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val | t2->as_base<T>().val);
}

template <typename T>
term_ptr __bitwise_xor(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val ^ t2->as_base<T>().val);
}

template <typename T>
term_ptr __neg(const term_ptr& t1) {
  return Term::make(-t1->as_base<T>().val);
}

template <typename T>
term_ptr __eq(const term_ptr& t1, const term_ptr& t2) {
  return Term::make<bool>(t1->as_base<T>().val == t2->as_base<T>().val);
}

template <typename T>
term_ptr __lt(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val < t2->as_base<T>().val);
}

template <typename T>
term_ptr __le(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val <= t2->as_base<T>().val);
}

template <typename T>
term_ptr __gt(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val > t2->as_base<T>().val);
}

template <typename T>
term_ptr __ge(const term_ptr& t1, const term_ptr& t2) {
  return Term::make(t1->as_base<T>().val >= t2->as_base<T>().val);
}

template <typename T>
term_ptr __cmp(const term_ptr& t1, const term_ptr& t2) {
  auto xval = t1->as_base<T>().val;
  auto yval = t2->as_base<T>().val;
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
  return Term::make(t1->as_base<string>().val + t2->as_base<string>().val);
}

term_ptr string_matches(const term_ptr& t1, const term_ptr& t2) {
  regex re(t2->as_base<string>().val);
  return Term::make<bool>(regex_match(t1->as_base<string>().val, re));
}

term_ptr string_starts_with(const term_ptr& t1, const term_ptr& t2) {
  auto str = t1->as_base<string>().val;
  auto pre = t2->as_base<string>().val;
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

term_ptr is_sat(const term_ptr& t1) {
  switch (smt_shim.is_sat(t1)) {
    case SmtStatus::sat: return Term::make<bool>(true);
    case SmtStatus::unsat: return Term::make<bool>(false);
    case SmtStatus::unknown: abort();
  }
  __builtin_unreachable();
}
/* INSERT 0 */

} // namespace funcs
/* INSERT 1 */

} // namespace flg
