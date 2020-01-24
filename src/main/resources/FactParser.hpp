#pragma once

#include <iostream>

// The Souffle header is here just to make sure that it is pulled in before the
// Antlr one, since the latter unsets the EOF macro it depends on.
#include <souffle/CompiledSouffle.h>
#include <antlr4-runtime.h>

#include "parsing/FormulogParser.h"
#include "parsing/FormulogLexer.h"

#include "Term.hpp"
#include "rels.hpp"

namespace flg {

using namespace std;
using namespace antlr4;

struct TermParser {
  term_ptr parse(FormulogParser::TermContext* ctx);
};

template <typename T>
struct FactParser {
  void parse(const string& file, T& rel);

  private:
  TermParser term_parser;
  void parse(FormulogParser::TabSeparatedTermLineContext* line, T& rel);
};


template <typename T>
void FactParser<T>::parse(const string& file, T& rel) {
  ifstream stream;
  stream.open(file);

  ANTLRInputStream input(stream);
  FormulogLexer lexer(&input);
  BufferedTokenStream tokens(&lexer);
  FormulogParser parser(&tokens);

  FormulogParser::TsvFileContext* tree = parser.tsvFile();
  for (auto& line : tree->tabSeparatedTermLine()) {
    parse(line, rel);
  }
}

template <typename T>
void FactParser<T>::parse(FormulogParser::TabSeparatedTermLineContext* line, T& rel) {
  Tuple<T::arity> tup;
  auto terms = line->term();
  if (terms.size() != T::arity) {
    cerr << "Wrong number of terms" << endl;
    abort();
  }
  size_t i;
  for (auto& term_ctx : terms) {
    tup[i++] = term_parser.parse(term_ctx);
  }
  rel.insert(tup);
}

term_ptr TermParser::parse(FormulogParser::TermContext* ctx) {
  return shared_ptr<Term>(nullptr);
}

} // namespace flg
