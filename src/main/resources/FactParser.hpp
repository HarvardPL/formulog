#pragma once

#include <cassert>
#include <cmath>
#include <iostream>
#include <limits>
#include <string>

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
  term_ptr parse(Symbol sym, const vector<FormulogParser::TermContext*>& ctxs);

  antlrcpp::Any visitHoleTerm(FormulogParser::HoleTermContext* ctx) override;
  antlrcpp::Any visitVarTerm(FormulogParser::VarTermContext* ctx) override;
  antlrcpp::Any visitStringTerm(FormulogParser::StringTermContext* ctx) override;
  antlrcpp::Any visitConsTerm(FormulogParser::ConsTermContext* ctx) override;
  antlrcpp::Any visitIndexedFunctor(FormulogParser::IndexedFunctorContext* ctx) override;
  antlrcpp::Any visitFoldTerm(FormulogParser::FoldTermContext* ctx) override;
  antlrcpp::Any visitTupleTerm(FormulogParser::TupleTermContext* ctx) override;
  antlrcpp::Any visitI32Term(FormulogParser::I32TermContext* ctx) override;
  antlrcpp::Any visitI64Term(FormulogParser::I64TermContext* ctx) override;
  antlrcpp::Any visitFloatTerm(FormulogParser::FloatTermContext* ctx) override;
  antlrcpp::Any visitDoubleTerm(FormulogParser::DoubleTermContext* ctx) override;
  antlrcpp::Any visitSpecialFPTerm(FormulogParser::SpecialFPTermContext* ctx) override;
  antlrcpp::Any visitRecordTerm(FormulogParser::RecordTermContext* ctx) override;
  antlrcpp::Any visitRecordUpdateTerm(FormulogParser::RecordUpdateTermContext* ctx) override;
  antlrcpp::Any visitUnopTerm(FormulogParser::UnopTermContext* ctx) override;
  antlrcpp::Any visitBinopTerm(FormulogParser::BinopTermContext* ctx) override;
  antlrcpp::Any visitListTerm(FormulogParser::ListTermContext* ctx) override;
  antlrcpp::Any visitParensTerm(FormulogParser::ParensTermContext* ctx) override;
  antlrcpp::Any visitFormulaTerm(FormulogParser::FormulaTermContext* ctx) override;
  antlrcpp::Any visitNotFormula(FormulogParser::NotFormulaContext* ctx) override;
  antlrcpp::Any visitBinopFormula(FormulogParser::BinopFormulaContext* ctx) override;
  antlrcpp::Any visitLetFormula(FormulogParser::LetFormulaContext* ctx) override;
  antlrcpp::Any visitQuantifiedFormula(FormulogParser::QuantifiedFormulaContext* ctx) override;
  antlrcpp::Any visitIteTerm(FormulogParser::IteTermContext* ctx) override;
  antlrcpp::Any visitTermSymFormula(FormulogParser::TermSymFormulaContext* ctx) override;
  antlrcpp::Any visitMatchExpr(FormulogParser::MatchExprContext* ctx) override;
  antlrcpp::Any visitLetExpr(FormulogParser::LetExprContext* ctx) override;
  antlrcpp::Any visitLetFunExpr(FormulogParser::LetFunExprContext* ctx) override;
  antlrcpp::Any visitIfExpr(FormulogParser::IfExprContext* ctx) override;

  [[noreturn]] static antlrcpp::Any die(const string& feature);
};

term_ptr TermParser::parse(Symbol sym, const vector<FormulogParser::TermContext*>& ctxs) {
  assert(symbol_arity(sym) == ctxs.size());
  switch (sym) {
/* INSERT 0 */
    default: __builtin_unreachable();
  }
}

antlrcpp::Any TermParser::visitHoleTerm(FormulogParser::HoleTermContext* ctx) {
  die("hole terms");
}

antlrcpp::Any TermParser::visitVarTerm(FormulogParser::VarTermContext* ctx) {
  die("variables");
}

antlrcpp::Any TermParser::visitStringTerm(FormulogParser::StringTermContext* ctx) {
  string s = ctx->QSTRING()->getText();
  s = s.substr(1, s.length() - 2);
  return Term::make<string>(s);
}

antlrcpp::Any TermParser::visitConsTerm(FormulogParser::ConsTermContext* ctx) {
  return parse(Symbol::cons, ctx->term());
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
  return parse(sym, ctx->termArgs()->term());
}

antlrcpp::Any TermParser::visitFoldTerm(FormulogParser::FoldTermContext* ctx) {
  die("fold");
}

antlrcpp::Any TermParser::visitTupleTerm(FormulogParser::TupleTermContext* ctx) {
  auto terms = ctx->tuple()->term();
  auto arity = terms.size();
  auto sym = lookup_tuple_symbol(arity);
  return parse(sym, terms);
}

antlrcpp::Any TermParser::visitI32Term(FormulogParser::I32TermContext* ctx) {
  return Term::make<int32_t>(stoi(ctx->val->getText(), nullptr, 0));
}

antlrcpp::Any TermParser::visitI64Term(FormulogParser::I64TermContext* ctx) {
  return Term::make<int64_t>(stoll(ctx->val->getText(), nullptr, 0));
}

antlrcpp::Any TermParser::visitFloatTerm(FormulogParser::FloatTermContext* ctx) {
  return Term::make<float>(stof(ctx->val->getText()));
}

antlrcpp::Any TermParser::visitDoubleTerm(FormulogParser::DoubleTermContext* ctx) {
  return Term::make<double>(stod(ctx->val->getText()));
}

antlrcpp::Any TermParser::visitSpecialFPTerm(FormulogParser::SpecialFPTermContext* ctx) {
  switch (ctx->val->getType()) {
    case FormulogParser::FP32_NAN:
      return Term::make<float>(nanf(""));
    case FormulogParser::FP32_POS_INFINITY:
      return Term::make<float>(numeric_limits<float>::infinity());
    case FormulogParser::FP32_NEG_INFINITY:
      return Term::make<float>(-numeric_limits<float>::infinity());
    case FormulogParser::FP64_NAN:
      return Term::make<double>(nan(""));
    case FormulogParser::FP64_POS_INFINITY:
      return Term::make<double>(numeric_limits<double>::infinity());
    case FormulogParser::FP64_NEG_INFINITY:
      return Term::make<double>(-numeric_limits<double>::infinity());
  }
  __builtin_unreachable();
}
antlrcpp::Any TermParser::visitRecordTerm(FormulogParser::RecordTermContext* ctx) {
  die("records");
}

antlrcpp::Any TermParser::visitRecordUpdateTerm(FormulogParser::RecordUpdateTermContext* ctx) {
  die("record updates");
}

antlrcpp::Any TermParser::visitUnopTerm(FormulogParser::UnopTermContext* ctx) {
  die("unops");
}

antlrcpp::Any TermParser::visitBinopTerm(FormulogParser::BinopTermContext* ctx) {
  die("binops");
}

antlrcpp::Any TermParser::visitListTerm(FormulogParser::ListTermContext* ctx) {
  term_ptr l = Term::make<Symbol::nil>();
  auto terms = ctx->list()->term();
  for (auto it = terms.crbegin(); it != terms.crend(); ++it) {
    term_ptr val = parse(*it);
    l = Term::make<Symbol::cons>(val, l);
  }
  return l;
}

antlrcpp::Any TermParser::visitParensTerm(FormulogParser::ParensTermContext* ctx) {
  return parse(ctx->term());
}

antlrcpp::Any TermParser::visitFormulaTerm(FormulogParser::FormulaTermContext* ctx) {
  die("formulas");
}

antlrcpp::Any TermParser::visitNotFormula(FormulogParser::NotFormulaContext* ctx) {
  die("formulas");
}

antlrcpp::Any TermParser::visitBinopFormula(FormulogParser::BinopFormulaContext* ctx) {
  die("formulas");
}

antlrcpp::Any TermParser::visitLetFormula(FormulogParser::LetFormulaContext* ctx) {
  die("formulas");
}

antlrcpp::Any TermParser::visitQuantifiedFormula(FormulogParser::QuantifiedFormulaContext* ctx) {
  die("formulas");
}

antlrcpp::Any TermParser::visitIteTerm(FormulogParser::IteTermContext* ctx) {
  die("formulas");
}

antlrcpp::Any TermParser::visitTermSymFormula(FormulogParser::TermSymFormulaContext* ctx) {
  die("formula variables");
}

antlrcpp::Any TermParser::visitMatchExpr(FormulogParser::MatchExprContext* ctx) {
  die("match expressions");
}

antlrcpp::Any TermParser::visitLetExpr(FormulogParser::LetExprContext* ctx) {
  die("let expressions");
}

antlrcpp::Any TermParser::visitLetFunExpr(FormulogParser::LetFunExprContext* ctx) {
  die("let fun expressions");
}

antlrcpp::Any TermParser::visitIfExpr(FormulogParser::IfExprContext* ctx) {
  die("if expressions");
}

[[noreturn]] antlrcpp::Any TermParser::die(const string& feature) {
  cerr << "Feature unsupported in external EDBs: " << feature << endl;
  abort();
}

term_ptr TermParser::parse(FormulogParser::TermContext* ctx) {
  term_ptr res = ctx->accept(this);
  return res;
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
  size_t i{0};
  for (auto& term_ctx : terms) {
    tup[i++] = term_parser.parse(term_ctx);
  }
  rel.insert(tup);
}

} // namespace flg
