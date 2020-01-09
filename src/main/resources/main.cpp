#include "Term.hpp"
#include "souffle/CompiledSouffle.h"
#include "Symbol.hpp"

using namespace flg;
using namespace std;

template <size_t N>
struct Tuple {
  array<shared_ptr<Term>, N> val;

  const shared_ptr<Term>& operator[](int idx) const {
    return val[idx];
  }

  shared_ptr<Term>& operator[](int idx) {
    return val[idx];
  }
};


template <size_t N>
ostream& operator<<(ostream& out, const Tuple<N>& tup)
{
  out << "[";
  for (size_t i = 0; i < N; ++i) {
    out << *tup[i].get();
    if (i < N - 1) {
      out << ", ";
    }
  }
  out << "]";
  return out;
}

// Inspired by the comparator in souffle/CompiledIndexUtils.h
template <unsigned... Columns>
struct Comparator;

template <unsigned First, unsigned... Rest>
struct Comparator<First, Rest...> {

  template <size_t N>
  int operator()(const Tuple<N>& a, const Tuple<N>& b) const {
		int cmp = Term::compare(a[First].get(), b[First].get());
		return cmp ? cmp : Comparator<Rest...>()(a, b);
  }

  template <size_t N>
  bool less(const Tuple<N>& a, const Tuple<N>& b) const {
		int cmp = Term::compare(a[First].get(), b[First].get());
		return cmp ? cmp < 0 : Comparator<Rest...>().less(a, b);
  }

  template <size_t N>
  bool equal(const Tuple<N>& a, const Tuple<N>& b) const {
		int cmp = Term::compare(a[First].get(), b[First].get());
		return cmp ? false : Comparator<Rest...>().equal(a, b);
  }
};

template <>
struct Comparator<> {

	template <size_t N>
  int operator()(const Tuple<N>& a, const Tuple<N>& b) const {
    return 0;
  }

	template <size_t N>
  bool less(const Tuple<N>& a, const Tuple<N>& b) const {
    return false;
  }

	template <size_t N>
  bool equal(const Tuple<N>& a, const Tuple<N>& b) const {
    return true;
  }
};

/* INSERT 0 */

void loadEdbs() {
/* INSERT 1 */
}

/* INSERT 2 */

void evaluate() {
/* INSERT 3 */
}

void printResults() {
/* INSERT 4 */
}

int main() {
  loadEdbs();
  evaluate();
  printResults();
  return 0;
}
