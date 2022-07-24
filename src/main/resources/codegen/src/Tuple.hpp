#pragma once

#include <array>
#include <iostream>
#include <string>

namespace flg {

using namespace std;

template <size_t N>
struct Tuple {
  array<term_ptr, N> val;

  inline const term_ptr& operator[](int idx) const {
    return val[idx];
  }

  inline term_ptr& operator[](int idx) {
    return val[idx];
  }

  inline bool operator<(const Tuple<N>& other) const {
    for (size_t i = 0; i < N; ++i) {
      int cmp = Term::compare_natural((*this)[i], other[i]);
      if (cmp != 0) {
        return cmp < 0;
      }
    }
    return false;
  }
};

template <size_t N>
inline ostream& operator<<(ostream& out, const Tuple<N>& tup)
{
  out << "(";
  for (size_t i = 0; i < N; ++i) {
    out << *tup[i];
    if (i < N - 1) {
      out << ", ";
    }
  }
  out << ")";
  return out;
}

template <typename Index>
inline void print_relation(const string& name, bool sorted, const Index& btree) {
  vector<typename Index::element_type> v(btree.begin(), btree.end());
  if (sorted) {
    sort(v.begin(), v.end());
  }
  for (const auto& tuple : v) {
    cout << name << tuple << '\n';
  }
  cout << flush;
}

// Inspired by the comparator in souffle/CompiledIndexUtils.h
template <unsigned... Columns>
struct Comparator;

template <unsigned First, unsigned... Rest>
struct Comparator<First, Rest...> {

  template <size_t N>
  inline int operator()(const Tuple<N>& a, const Tuple<N>& b) const {
    int cmp = Term::compare(a[First], b[First]);
    return cmp ? cmp : Comparator<Rest...>()(a, b);
  }

  template <size_t N>
  inline bool less(const Tuple<N>& a, const Tuple<N>& b) const {
    int cmp = Term::compare(a[First], b[First]);
    return cmp ? cmp < 0 : Comparator<Rest...>().less(a, b);
  }

  template <size_t N>
  inline bool equal(const Tuple<N>& a, const Tuple<N>& b) const {
    int cmp = Term::compare(a[First], b[First]);
    return cmp ? false : Comparator<Rest...>().equal(a, b);
  }
};

template <>
struct Comparator<> {

  template <size_t N>
  inline int operator()(const Tuple<N>& a, const Tuple<N>& b) const {
    return 0;
  }

  template <size_t N>
  inline bool less(const Tuple<N>& a, const Tuple<N>& b) const {
    return false;
  }

  template <size_t N>
  inline bool equal(const Tuple<N>& a, const Tuple<N>& b) const {
    return true;
  }
};

} // namespace flg
