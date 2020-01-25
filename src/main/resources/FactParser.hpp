#pragma once

#include <iostream>

// The Souffle header is here just to make sure that it is pulled in before the
// Antlr one, since the latter unsets the EOF macro it depends on.
#include <souffle/CompiledSouffle.h>
#include <antlr4-runtime.h>

#include "parsing/FormulogParser.h"
#include "parsing/FormulogLexer.h"
#include "parsing/FormulogBaseVisitor.h"

#include "Term.hpp"
#include "rels.hpp"

namespace flg {

using namespace std;
using namespace antlr4;

class TermParser : private FormulogBaseVisitor {
  public:
  term_ptr parse(FormulogParser::TermContext* ctx);

  private:
  term_ptr* parse(vector<FormulogParser::TermContext*> ctxs);

  antlrcpp::Any visitHoleTerm(FormulogParser::HoleTermContext* ctx) override;
  antlrcpp::Any visitVarTerm(FormulogParser::VarTermContext* ctx) override;
  antlrcpp::Any visitStringTerm(FormulogParser::StringTermContext* ctx) override;
  antlrcpp::Any visitConsTerm(FormulogParser::ConsTermContext* ctx) override;
  antlrcpp::Any visitIndexedFunctor(FormulogParser::IndexedFunctorContext* ctx) override;
  antlrcpp::Any visitFoldTerm(FormulogParser::FoldTermContext* ctx) override;
  antlrcpp::Any visitTupleTerm(FormulogParser::TupleTermContext* ctx) override;

  static antlrcpp::Any die(const string& feature);
};

term_ptr* TermParser::parse(vector<FormulogParser::TermContext*> ctxs) {
  term_ptr* a = new term_ptr[ctxs.size()];
  size_t i{0};
  for (auto& ctx : ctxs) {
		const auto& t = parse(ctx);
    a[i++] = reinterpret_cast<const term_ptr&>(t);
  }
  return a;
}

antlrcpp::Any TermParser::visitHoleTerm(FormulogParser::HoleTermContext* ctx) {
  return die("hole terms");
}

antlrcpp::Any TermParser::visitVarTerm(FormulogParser::VarTermContext* ctx) {
  return die("variables");
}

antlrcpp::Any TermParser::visitStringTerm(FormulogParser::StringTermContext* ctx) {
  return Term::make<string>(ctx->QSTRING()->getText());
}

antlrcpp::Any TermParser::visitConsTerm(FormulogParser::ConsTermContext* ctx) {
  return Term::make(Symbol::cons, 2, parse(ctx->term()));
}

antlrcpp::Any TermParser::visitIndexedFunctor(FormulogParser::IndexedFunctorContext* ctx) {
  if (!ctx->parameterList()->parameter().empty()) {
    die("parameterized terms");
  }
  string name = ctx->id->getText();
  if (name == "true") {
    return Term::make<bool>(true);
  }
  if (name == "false") {
    return Term::make<bool>(false);
  }
  auto sym = lookup_symbol(name);
  auto arity = symbol_arity(sym);
  auto args = parse(ctx->termArgs()->term());
  return Term::make(sym, arity, args); 
}

antlrcpp::Any TermParser::visitFoldTerm(FormulogParser::FoldTermContext* ctx) {
  return die("fold");
}

antlrcpp::Any TermParser::visitTupleTerm(FormulogParser::TupleTermContext* ctx) {
  auto terms = ctx->tuple()->term();
  auto arity = terms.size();
  auto sym = lookup_tuple_symbol(arity);
  auto args = parse(terms);
  return Term::make(sym, arity, args);
}

antlrcpp::Any TermParser::die(const string& feature) {
  cerr << "Feature unsupported in external EDBs: " << feature << endl;
  abort();
  return nullptr;
}

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
