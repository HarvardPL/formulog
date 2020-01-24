
// Generated from Formulog.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"
#include "FormulogVisitor.h"


/**
 * This class provides an empty implementation of FormulogVisitor, which can be
 * extended to create a visitor which only needs to handle a subset of the available methods.
 */
class  FormulogBaseVisitor : public FormulogVisitor {
public:

  virtual antlrcpp::Any visitProg(FormulogParser::ProgContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTsvFile(FormulogParser::TsvFileContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTabSeparatedTermLine(FormulogParser::TabSeparatedTermLineContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFunDecl(FormulogParser::FunDeclContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRelDecl(FormulogParser::RelDeclContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeAlias(FormulogParser::TypeAliasContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeDecl(FormulogParser::TypeDeclContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitUninterpFunDecl(FormulogParser::UninterpFunDeclContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitUninterpSortDecl(FormulogParser::UninterpSortDeclContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFunDefLHS(FormulogParser::FunDefLHSContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFunDefs(FormulogParser::FunDefsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitConstructorType(FormulogParser::ConstructorTypeContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitVarTypeList(FormulogParser::VarTypeListContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeList(FormulogParser::TypeListContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeVar(FormulogParser::TypeVarContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitParenType(FormulogParser::ParenTypeContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeRef(FormulogParser::TypeRefContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTupleType(FormulogParser::TupleTypeContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitParameterList(FormulogParser::ParameterListContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitWildCardParam(FormulogParser::WildCardParamContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeParam(FormulogParser::TypeParamContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitIntParam(FormulogParser::IntParamContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeDefLHS(FormulogParser::TypeDefLHSContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTypeDefRHS(FormulogParser::TypeDefRHSContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitAdtDef(FormulogParser::AdtDefContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRecordDef(FormulogParser::RecordDefContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRecordEntryDef(FormulogParser::RecordEntryDefContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitAnnotation(FormulogParser::AnnotationContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitClauseStmt(FormulogParser::ClauseStmtContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFactStmt(FormulogParser::FactStmtContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitQueryStmt(FormulogParser::QueryStmtContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitClause(FormulogParser::ClauseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFact(FormulogParser::FactContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitQuery(FormulogParser::QueryContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPredicate(FormulogParser::PredicateContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitIndexedFunctor(FormulogParser::IndexedFunctorContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTermArgs(FormulogParser::TermArgsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitQuantifiedFormula(FormulogParser::QuantifiedFormulaContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitBinopTerm(FormulogParser::BinopTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitMatchExpr(FormulogParser::MatchExprContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFunctorTerm(FormulogParser::FunctorTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitI32Term(FormulogParser::I32TermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitNotFormula(FormulogParser::NotFormulaContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitLetExpr(FormulogParser::LetExprContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFloatTerm(FormulogParser::FloatTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRecordTerm(FormulogParser::RecordTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitLetFormula(FormulogParser::LetFormulaContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitUnopTerm(FormulogParser::UnopTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitIfExpr(FormulogParser::IfExprContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitHoleTerm(FormulogParser::HoleTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitListTerm(FormulogParser::ListTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitVarTerm(FormulogParser::VarTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitStringTerm(FormulogParser::StringTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFormulaTerm(FormulogParser::FormulaTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitConsTerm(FormulogParser::ConsTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTermSymFormula(FormulogParser::TermSymFormulaContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitParensTerm(FormulogParser::ParensTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitI64Term(FormulogParser::I64TermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitIteTerm(FormulogParser::IteTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFoldTerm(FormulogParser::FoldTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSpecialFPTerm(FormulogParser::SpecialFPTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitDoubleTerm(FormulogParser::DoubleTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitLetFunExpr(FormulogParser::LetFunExprContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitBinopFormula(FormulogParser::BinopFormulaContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitOutermostCtor(FormulogParser::OutermostCtorContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTupleTerm(FormulogParser::TupleTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRecordUpdateTerm(FormulogParser::RecordUpdateTermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRecordEntries(FormulogParser::RecordEntriesContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitRecordEntry(FormulogParser::RecordEntryContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitLetBind(FormulogParser::LetBindContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitNonEmptyTermList(FormulogParser::NonEmptyTermListContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitList(FormulogParser::ListContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTuple(FormulogParser::TupleContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitMatchClause(FormulogParser::MatchClauseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPatterns(FormulogParser::PatternsContext *ctx) override {
    return visitChildren(ctx);
  }


};

