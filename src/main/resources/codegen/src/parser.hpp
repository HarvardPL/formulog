#pragma once

#include <iostream>
#include <stdexcept>
#include <sstream>
#include <string>

#include "Term.hpp"
#include "Tuple.hpp"

namespace flg {

namespace parser {

using namespace std;

// Exception class thrown when parsing facts
class parsing_error : public logic_error {
  using logic_error::logic_error;
};

term_ptr parse_term(const string& term);

template <typename T>
inline void parse_facts(istream& in, T& rel) {
  // Parse each fact of the stream on a new line
  string line;
  while (getline(in, line)) {
    istringstream ss(line);
    Tuple<T::arity> value;
    // Tab-separated term format
    string term;
    size_t count = 0;
    while (getline(ss, term, '\t')) {
      if (count >= T::arity) {
        throw parsing_error("Too many terms in tab-separated line");
      }
      value[count++] = parse_term(term);
    }
    if (count != T::arity) {
      throw parsing_error("Too few terms in tab-separated line");
    }
    rel.insert(value);
  }
}

} // namespace parser

using parser::parse_facts;

} // namespace flg
