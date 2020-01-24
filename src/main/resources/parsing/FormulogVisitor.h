
// Generated from Formulog.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"
#include "FormulogParser.h"



/**
 * This class defines an abstract visitor for a parse tree
 * produced by FormulogParser.
 */
class  FormulogVisitor : public antlr4::tree::AbstractParseTreeVisitor {
public:

  /**
   * Visit parse trees produced by FormulogParser.
   */
    virtual antlrcpp::Any visitProg(FormulogParser::ProgContext *context) = 0;

    virtual antlrcpp::Any visitTsvFile(FormulogParser::TsvFileContext *context) = 0;

    virtual antlrcpp::Any visitTabSeparatedTermLine(FormulogParser::TabSeparatedTermLineContext *context) = 0;

    virtual antlrcpp::Any visitFunDecl(FormulogParser::FunDeclContext *context) = 0;

    virtual antlrcpp::Any visitRelDecl(FormulogParser::RelDeclContext *context) = 0;

    virtual antlrcpp::Any visitTypeAlias(FormulogParser::TypeAliasContext *context) = 0;

    virtual antlrcpp::Any visitTypeDecl(FormulogParser::TypeDeclContext *context) = 0;

    virtual antlrcpp::Any visitUninterpFunDecl(FormulogParser::UninterpFunDeclContext *context) = 0;

    virtual antlrcpp::Any visitUninterpSortDecl(FormulogParser::UninterpSortDeclContext *context) = 0;

    virtual antlrcpp::Any visitFunDefLHS(FormulogParser::FunDefLHSContext *context) = 0;

    virtual antlrcpp::Any visitFunDefs(FormulogParser::FunDefsContext *context) = 0;

    virtual antlrcpp::Any visitConstructorType(FormulogParser::ConstructorTypeContext *context) = 0;

    virtual antlrcpp::Any visitVarTypeList(FormulogParser::VarTypeListContext *context) = 0;

    virtual antlrcpp::Any visitTypeList(FormulogParser::TypeListContext *context) = 0;

    virtual antlrcpp::Any visitTypeVar(FormulogParser::TypeVarContext *context) = 0;

    virtual antlrcpp::Any visitParenType(FormulogParser::ParenTypeContext *context) = 0;

    virtual antlrcpp::Any visitTypeRef(FormulogParser::TypeRefContext *context) = 0;

    virtual antlrcpp::Any visitTupleType(FormulogParser::TupleTypeContext *context) = 0;

    virtual antlrcpp::Any visitParameterList(FormulogParser::ParameterListContext *context) = 0;

    virtual antlrcpp::Any visitWildCardParam(FormulogParser::WildCardParamContext *context) = 0;

    virtual antlrcpp::Any visitTypeParam(FormulogParser::TypeParamContext *context) = 0;

    virtual antlrcpp::Any visitIntParam(FormulogParser::IntParamContext *context) = 0;

    virtual antlrcpp::Any visitTypeDefLHS(FormulogParser::TypeDefLHSContext *context) = 0;

    virtual antlrcpp::Any visitTypeDefRHS(FormulogParser::TypeDefRHSContext *context) = 0;

    virtual antlrcpp::Any visitAdtDef(FormulogParser::AdtDefContext *context) = 0;

    virtual antlrcpp::Any visitRecordDef(FormulogParser::RecordDefContext *context) = 0;

    virtual antlrcpp::Any visitRecordEntryDef(FormulogParser::RecordEntryDefContext *context) = 0;

    virtual antlrcpp::Any visitAnnotation(FormulogParser::AnnotationContext *context) = 0;

    virtual antlrcpp::Any visitClauseStmt(FormulogParser::ClauseStmtContext *context) = 0;

    virtual antlrcpp::Any visitFactStmt(FormulogParser::FactStmtContext *context) = 0;

    virtual antlrcpp::Any visitQueryStmt(FormulogParser::QueryStmtContext *context) = 0;

    virtual antlrcpp::Any visitClause(FormulogParser::ClauseContext *context) = 0;

    virtual antlrcpp::Any visitFact(FormulogParser::FactContext *context) = 0;

    virtual antlrcpp::Any visitQuery(FormulogParser::QueryContext *context) = 0;

    virtual antlrcpp::Any visitPredicate(FormulogParser::PredicateContext *context) = 0;

    virtual antlrcpp::Any visitIndexedFunctor(FormulogParser::IndexedFunctorContext *context) = 0;

    virtual antlrcpp::Any visitTermArgs(FormulogParser::TermArgsContext *context) = 0;

    virtual antlrcpp::Any visitQuantifiedFormula(FormulogParser::QuantifiedFormulaContext *context) = 0;

    virtual antlrcpp::Any visitBinopTerm(FormulogParser::BinopTermContext *context) = 0;

    virtual antlrcpp::Any visitMatchExpr(FormulogParser::MatchExprContext *context) = 0;

    virtual antlrcpp::Any visitFunctorTerm(FormulogParser::FunctorTermContext *context) = 0;

    virtual antlrcpp::Any visitI32Term(FormulogParser::I32TermContext *context) = 0;

    virtual antlrcpp::Any visitNotFormula(FormulogParser::NotFormulaContext *context) = 0;

    virtual antlrcpp::Any visitLetExpr(FormulogParser::LetExprContext *context) = 0;

    virtual antlrcpp::Any visitFloatTerm(FormulogParser::FloatTermContext *context) = 0;

    virtual antlrcpp::Any visitRecordTerm(FormulogParser::RecordTermContext *context) = 0;

    virtual antlrcpp::Any visitLetFormula(FormulogParser::LetFormulaContext *context) = 0;

    virtual antlrcpp::Any visitUnopTerm(FormulogParser::UnopTermContext *context) = 0;

    virtual antlrcpp::Any visitIfExpr(FormulogParser::IfExprContext *context) = 0;

    virtual antlrcpp::Any visitHoleTerm(FormulogParser::HoleTermContext *context) = 0;

    virtual antlrcpp::Any visitListTerm(FormulogParser::ListTermContext *context) = 0;

    virtual antlrcpp::Any visitVarTerm(FormulogParser::VarTermContext *context) = 0;

    virtual antlrcpp::Any visitStringTerm(FormulogParser::StringTermContext *context) = 0;

    virtual antlrcpp::Any visitFormulaTerm(FormulogParser::FormulaTermContext *context) = 0;

    virtual antlrcpp::Any visitConsTerm(FormulogParser::ConsTermContext *context) = 0;

    virtual antlrcpp::Any visitTermSymFormula(FormulogParser::TermSymFormulaContext *context) = 0;

    virtual antlrcpp::Any visitParensTerm(FormulogParser::ParensTermContext *context) = 0;

    virtual antlrcpp::Any visitI64Term(FormulogParser::I64TermContext *context) = 0;

    virtual antlrcpp::Any visitIteTerm(FormulogParser::IteTermContext *context) = 0;

    virtual antlrcpp::Any visitFoldTerm(FormulogParser::FoldTermContext *context) = 0;

    virtual antlrcpp::Any visitSpecialFPTerm(FormulogParser::SpecialFPTermContext *context) = 0;

    virtual antlrcpp::Any visitDoubleTerm(FormulogParser::DoubleTermContext *context) = 0;

    virtual antlrcpp::Any visitLetFunExpr(FormulogParser::LetFunExprContext *context) = 0;

    virtual antlrcpp::Any visitBinopFormula(FormulogParser::BinopFormulaContext *context) = 0;

    virtual antlrcpp::Any visitOutermostCtor(FormulogParser::OutermostCtorContext *context) = 0;

    virtual antlrcpp::Any visitTupleTerm(FormulogParser::TupleTermContext *context) = 0;

    virtual antlrcpp::Any visitRecordUpdateTerm(FormulogParser::RecordUpdateTermContext *context) = 0;

    virtual antlrcpp::Any visitRecordEntries(FormulogParser::RecordEntriesContext *context) = 0;

    virtual antlrcpp::Any visitRecordEntry(FormulogParser::RecordEntryContext *context) = 0;

    virtual antlrcpp::Any visitLetBind(FormulogParser::LetBindContext *context) = 0;

    virtual antlrcpp::Any visitNonEmptyTermList(FormulogParser::NonEmptyTermListContext *context) = 0;

    virtual antlrcpp::Any visitList(FormulogParser::ListContext *context) = 0;

    virtual antlrcpp::Any visitTuple(FormulogParser::TupleContext *context) = 0;

    virtual antlrcpp::Any visitMatchClause(FormulogParser::MatchClauseContext *context) = 0;

    virtual antlrcpp::Any visitPatterns(FormulogParser::PatternsContext *context) = 0;


};

