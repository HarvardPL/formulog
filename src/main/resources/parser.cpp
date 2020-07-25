#include <algorithm>
#include <cassert>
#include <cmath>
#include <regex>
#include <unordered_map>
#include <vector>

#include <boost/optional.hpp>

#include "parser.hpp"

namespace flg {

namespace parser {

using boost::optional;

term_ptr construct_generic_term(Symbol sym, const vector<term_ptr>& terms) {
  if (symbol_arity(sym) != terms.size()) {
    string message = "Expected arity ";
    message += to_string(symbol_arity(sym));
    message += " for symbol (ID ";
    message += to_string(static_cast<int>(sym));
    message += "), got arity ";
    message += to_string(terms.size());
    throw parsing_error(message);
  }
  switch (sym) {
/* INSERT 0 */
    default:
      throw parsing_error(
        "Invalid symbol (ID " +
        to_string(static_cast<int>(sym)) +
        ") used to construct term"
      );
  }
}

// A class that represents the intermediate parsing state of a term
class TermParser {
  const string& buffer;
  size_t pos;

  public:
  TermParser(const string& term) : buffer(term), pos(0) {}

  inline void take_whitespace();
  inline bool take_string(const string& str);
  inline optional<smatch> take_regex(const regex& rgx);

  inline char peek();
  inline bool empty();

  inline term_ptr take_term();
  inline vector<term_ptr> take_terms();
  inline term_ptr take_tuple_or_parens();
  inline term_ptr take_list();
  inline term_ptr take_constructor();
  inline term_ptr take_string();
  inline term_ptr take_numeric();
};

inline void TermParser::take_whitespace() {
  while (pos < buffer.size() && buffer[pos] == ' ') {
    ++pos;
  }
}

inline bool TermParser::take_string(const string& str) {
  if (
    pos + str.size() <= buffer.size() &&
    equal(str.begin(), str.end(), buffer.begin() + pos)
  ) {
    pos += str.size();
    return true;
  }
  return false;
}

inline optional<smatch> TermParser::take_regex(const regex& rgx) {
  smatch m;
  if (regex_search(buffer.begin() + pos, buffer.end(), m, rgx)) {
    pos += m.length();
    return m;
  }
  return optional<smatch>();
}

inline char TermParser::peek() {
  take_whitespace();
  if (pos == buffer.size()) {
    throw parsing_error("Unexpected end of term");
  }
  return buffer[pos];
}

inline bool TermParser::empty() {
  take_whitespace();
  return pos == buffer.size();
}

inline term_ptr TermParser::take_term() {
  take_whitespace();
  term_ptr retval;

  // Determine type of term based on first character
  char c = peek();
  if (c == '"') {
    retval = take_string();
  } else if (c == '+' || c == '-' || ('0' <= c && c <= '9')) {
    retval = take_numeric();
  } else if (c == '(') {
    retval = take_tuple_or_parens();
  } else if (c == '[') {
    retval = take_list();
  } else if (c >= 'a' && c <= 'z') {
    retval = take_constructor();
  } else {
    throw parsing_error(string("Unexpected character: ") + c);
  }

  // Handle right-associative cons (::) operator
  if (!empty() && peek() == ':') {
    ++pos;
    if (peek() != ':') {
      throw parsing_error("Found first ':', expected a second ':' for cons");
    }
    ++pos;
    return Term::make<Symbol::cons>(retval, take_term());
  }

  return retval;
}

inline vector<term_ptr> TermParser::take_terms() {
  vector<term_ptr> retval;
  retval.push_back(take_term());
  while (!empty() && peek() == ',') {
    ++pos;
    retval.push_back(take_term());
  }
  return retval;
}

inline term_ptr TermParser::take_tuple_or_parens() {
  assert(buffer[pos] == '('); // Sanity check
  ++pos;
  vector<term_ptr> terms = take_terms();
  if (peek() != ')') {
    throw parsing_error("Expected character ')' to close parens");
  }
  ++pos;
  if (terms.size() == 1) {
    // Parentheses case
    return terms[0];
  }
  // Tuple case
  auto sym = lookup_tuple_symbol(terms.size());
  return construct_generic_term(sym, terms);
}

inline term_ptr TermParser::take_list() {
  assert(buffer[pos] == '['); // Sanity check
  ++pos;
  // Case: empty list (equivalent to nil)
  if (peek() == ']') {
    ++pos;
    return Term::make<Symbol::nil>();
  }
  vector<term_ptr> terms = take_terms();
  if (peek() != ']') {
    throw parsing_error("Expected character ']' to close list");
  }
  ++pos;
  // Construct the list
  term_ptr retval = Term::make<Symbol::nil>();
  for (auto it = terms.crbegin(); it != terms.crend(); ++it) {
    retval = Term::make<Symbol::cons>(*it, retval);
  }
  return retval;
}

inline term_ptr TermParser::take_constructor() {
  static const unordered_map<string, term_ptr> literals = {
    {"true", Term::make<bool>(true)},
    {"false", Term::make<bool>(false)},
    {"true", Term::make<bool>(true)},
    {"fp32_nan", Term::make<float>(nanf(""))},
    {"fp32_pos_infinity", Term::make<float>(INFINITY)},
    {"fp32_neg_infinity", Term::make<float>(-INFINITY)},
    {"fp64_nan", Term::make<double>(nan(""))},
    {"fp64_pos_infinity", Term::make<double>(INFINITY)},
    {"fp64_neg_infinity", Term::make<double>(-INFINITY)},
  };
  static const regex name_re(R"(^[a-z][a-zA-Z0-9_]*)");
  auto match = take_regex(name_re);
  assert(match);
  string name = match->str();
  const auto it = literals.find(name);
  if (it != literals.end()) {
    return it->second;
  }
  auto sym = lookup_symbol(name);
  vector<term_ptr> terms;
  if (!empty() && peek() == '(') {
    ++pos;
    if (symbol_arity(sym) != 0) {
      terms = take_terms();
    }
    if (peek() != ')') {
      throw parsing_error("Expected ')' to close constructor");
    }
    ++pos;
  }
  return construct_generic_term(sym, terms);
}

inline term_ptr TermParser::take_string() {
  // Compatibility Note:
  //   Currently, the Formulog parser does not support escape sequences, so I am
  //   also not supporting escape sequences in the parsing step. This makes it
  //   impossible to create strings with the characters \", \n, \t, \r, etc.
  assert(buffer[pos] == '"');
  ++pos;
  static const regex string_re(R"(^[^"]*")");
  auto match = take_regex(string_re);
  if (!match) {
    throw parsing_error("Could not detect end of string literal");
  }
  string contents = match->str();
  contents.pop_back(); // Remove trailing " character
  return Term::make<string>(contents);
}

inline term_ptr TermParser::take_numeric() {
  // Parse sign
  int sign = 1;
  const char signchar = peek();
  if (signchar == '+' || signchar == '-') {
    if (signchar == '-') {
      sign = -1;
    }
    ++pos;
  }

  // Handle hexadecimal case
  static const regex hex_re(R"(^0(?:x|X)([0-9a-fA-F]+)([Ll]?)\b)");
  if (auto match = take_regex(hex_re)) {
    if (match->length(2)) {
      auto value = stoll(match->str(1), nullptr, 16);
      return Term::make<int64_t>(sign * value);
    } else {
      auto value = stoi(match->str(1), nullptr, 16);
      return Term::make<int32_t>(sign * value);
    }
  }

  // Handle decimal case
  static const regex dec_re(R"(^([0-9]+)([Ll]?)\b(?!\.))");
  if (auto match = take_regex(dec_re)) {
    if (match->length(2)) {
      auto value = stoll(match->str(1));
      return Term::make<int64_t>(sign * value);
    } else {
      auto value = stoi(match->str(1));
      return Term::make<int32_t>(sign * value);
    }
  }

  // Handle floating-point case
  static const regex fp_re(
    R"(^((?:[0-9]*\.[0-9]+|[0-9]+)(?:[Ee][+-]?[0-9]+)?)([FfDd]?)\b)"
  );
  if (auto match = take_regex(fp_re)) {
    string suffix = match->str(2);
    if (suffix == "f" || suffix == "F") {
      auto value = stof(match->str(1));
      return Term::make<float>(sign * value);
    } else {
      auto value = stod(match->str(1));
      return Term::make<double>(sign * value);
    }
  }

  throw parsing_error("Could not identify numeric value");
}

term_ptr parse_term(const string& term) {
  TermParser context(term);
  term_ptr retval = context.take_term();
  if (!context.empty()) {
    throw parsing_error("Unexpected trailing characters in term: " + term);
  }
  return retval;
}

} // namespace parser

using parser::parse_facts;

} // namespace flg
