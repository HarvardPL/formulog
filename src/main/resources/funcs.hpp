#ifndef FUNCTIONS_HPP__
#define FUNCTIONS_HPP__

#include "Term.hpp"

namespace flg {

namespace funcs {

using namespace std;

template <typename T>
term_ptr add(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val + y->val);
}

template <typename T>
term_ptr sub(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val - y->val);
}

template <typename T>
term_ptr mul(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val * y->val);
}

template <typename T>
term_ptr div(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val / y->val);
}

template <typename T>
term_ptr rem(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val % y->val);
}

template <typename T>
term_ptr bitwise_and(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val & y->val);
}

template <typename T>
term_ptr bitwise_or(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val | y->val);
}

template <typename T>
term_ptr bitwise_xor(const term_ptr& t1, const term_ptr& t2) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  auto y = reinterpret_cast<BaseTerm<T>*>(t2.get());
  return Term::make(x->val ^ y->val);
}

template <typename T>
term_ptr neg(const term_ptr& t1) {
  auto x = reinterpret_cast<BaseTerm<T>*>(t1.get());
  return Term::make(-x->val);
}
/* INSERT 0 */

} // namespace funcs
/* INSERT 1 */

} // namespace flg

#endif
