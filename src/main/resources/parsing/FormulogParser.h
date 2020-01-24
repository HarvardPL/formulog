
// Generated from Formulog.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"




class  FormulogParser : public antlr4::Parser {
public:
  enum {
    T__0 = 1, T__1 = 2, T__2 = 3, T__3 = 4, T__4 = 5, T__5 = 6, T__6 = 7, 
    T__7 = 8, T__8 = 9, T__9 = 10, T__10 = 11, T__11 = 12, T__12 = 13, T__13 = 14, 
    T__14 = 15, T__15 = 16, T__16 = 17, T__17 = 18, T__18 = 19, T__19 = 20, 
    T__20 = 21, T__21 = 22, T__22 = 23, T__23 = 24, T__24 = 25, T__25 = 26, 
    T__26 = 27, T__27 = 28, T__28 = 29, T__29 = 30, T__30 = 31, T__31 = 32, 
    T__32 = 33, T__33 = 34, AND = 35, OR = 36, IMP = 37, IFF = 38, NOT = 39, 
    FORMULA_EQ = 40, INPUT = 41, OUTPUT = 42, FP32_NAN = 43, FP32_POS_INFINITY = 44, 
    FP32_NEG_INFINITY = 45, FP64_NAN = 46, FP64_POS_INFINITY = 47, FP64_NEG_INFINITY = 48, 
    TYPEVAR = 49, XVAR = 50, VAR = 51, INT = 52, HEX = 53, FP32 = 54, FP64 = 55, 
    I64 = 56, LT = 57, LTE = 58, GT = 59, GTE = 60, MUL = 61, DIV = 62, 
    REM = 63, PLUS = 64, MINUS = 65, BANG = 66, CARET = 67, AMP = 68, BARBAR = 69, 
    AMPAMP = 70, ISNOT = 71, EQ = 72, NEQ = 73, FORALL = 74, EXISTS = 75, 
    HOLE = 76, NEWLINE = 77, TAB = 78, SPACES = 79, COMMENT = 80, XID = 81, 
    ID = 82, QSTRING = 83
  };

  enum {
    RuleProg = 0, RuleTsvFile = 1, RuleTabSeparatedTermLine = 2, RuleMetadata = 3, 
    RuleFunDefLHS = 4, RuleFunDefs = 5, RuleConstructorType = 6, RuleVarTypeList = 7, 
    RuleTypeList = 8, RuleType0 = 9, RuleType = 10, RuleParameterList = 11, 
    RuleParameter = 12, RuleTypeDefLHS = 13, RuleTypeDefRHS = 14, RuleAdtDef = 15, 
    RuleRecordDef = 16, RuleRecordEntryDef = 17, RuleAnnotation = 18, RuleStmt = 19, 
    RuleClause = 20, RuleFact = 21, RuleQuery = 22, RulePredicate = 23, 
    RuleFunctor = 24, RuleTermArgs = 25, RuleTerm = 26, RuleRecordEntries = 27, 
    RuleRecordEntry = 28, RuleLetBind = 29, RuleNonEmptyTermList = 30, RuleList = 31, 
    RuleTuple = 32, RuleMatchClause = 33, RulePatterns = 34
  };

  FormulogParser(antlr4::TokenStream *input);
  ~FormulogParser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class ProgContext;
  class TsvFileContext;
  class TabSeparatedTermLineContext;
  class MetadataContext;
  class FunDefLHSContext;
  class FunDefsContext;
  class ConstructorTypeContext;
  class VarTypeListContext;
  class TypeListContext;
  class Type0Context;
  class TypeContext;
  class ParameterListContext;
  class ParameterContext;
  class TypeDefLHSContext;
  class TypeDefRHSContext;
  class AdtDefContext;
  class RecordDefContext;
  class RecordEntryDefContext;
  class AnnotationContext;
  class StmtContext;
  class ClauseContext;
  class FactContext;
  class QueryContext;
  class PredicateContext;
  class FunctorContext;
  class TermArgsContext;
  class TermContext;
  class RecordEntriesContext;
  class RecordEntryContext;
  class LetBindContext;
  class NonEmptyTermListContext;
  class ListContext;
  class TupleContext;
  class MatchClauseContext;
  class PatternsContext; 

  class  ProgContext : public antlr4::ParserRuleContext {
  public:
    ProgContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EOF();
    std::vector<MetadataContext *> metadata();
    MetadataContext* metadata(size_t i);
    std::vector<StmtContext *> stmt();
    StmtContext* stmt(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ProgContext* prog();

  class  TsvFileContext : public antlr4::ParserRuleContext {
  public:
    TsvFileContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EOF();
    std::vector<TabSeparatedTermLineContext *> tabSeparatedTermLine();
    TabSeparatedTermLineContext* tabSeparatedTermLine(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TsvFileContext* tsvFile();

  class  TabSeparatedTermLineContext : public antlr4::ParserRuleContext {
  public:
    TabSeparatedTermLineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NEWLINE();
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TAB();
    antlr4::tree::TerminalNode* TAB(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TabSeparatedTermLineContext* tabSeparatedTermLine();

  class  MetadataContext : public antlr4::ParserRuleContext {
  public:
    MetadataContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    MetadataContext() : antlr4::ParserRuleContext() { }
    void copyFrom(MetadataContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  UninterpSortDeclContext : public MetadataContext {
  public:
    UninterpSortDeclContext(MetadataContext *ctx);

    TypeDefLHSContext *typeDefLHS();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  RelDeclContext : public MetadataContext {
  public:
    RelDeclContext(MetadataContext *ctx);

    antlr4::Token *relType = nullptr;
    antlr4::tree::TerminalNode *ID();
    TypeListContext *typeList();
    antlr4::tree::TerminalNode *INPUT();
    antlr4::tree::TerminalNode *OUTPUT();
    std::vector<AnnotationContext *> annotation();
    AnnotationContext* annotation(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  UninterpFunDeclContext : public MetadataContext {
  public:
    UninterpFunDeclContext(MetadataContext *ctx);

    ConstructorTypeContext *constructorType();
    TypeContext *type();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  FunDeclContext : public MetadataContext {
  public:
    FunDeclContext(MetadataContext *ctx);

    FunDefsContext *funDefs();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  TypeAliasContext : public MetadataContext {
  public:
    TypeAliasContext(MetadataContext *ctx);

    TypeDefLHSContext *typeDefLHS();
    antlr4::tree::TerminalNode *EQ();
    TypeContext *type();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  TypeDeclContext : public MetadataContext {
  public:
    TypeDeclContext(MetadataContext *ctx);

    std::vector<TypeDefLHSContext *> typeDefLHS();
    TypeDefLHSContext* typeDefLHS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQ();
    antlr4::tree::TerminalNode* EQ(size_t i);
    std::vector<TypeDefRHSContext *> typeDefRHS();
    TypeDefRHSContext* typeDefRHS(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  MetadataContext* metadata();

  class  FunDefLHSContext : public antlr4::ParserRuleContext {
  public:
    FormulogParser::VarTypeListContext *args = nullptr;;
    FormulogParser::TypeContext *retType = nullptr;;
    FunDefLHSContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    VarTypeListContext *varTypeList();
    TypeContext *type();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  FunDefLHSContext* funDefLHS();

  class  FunDefsContext : public antlr4::ParserRuleContext {
  public:
    FunDefsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<FunDefLHSContext *> funDefLHS();
    FunDefLHSContext* funDefLHS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> EQ();
    antlr4::tree::TerminalNode* EQ(size_t i);
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  FunDefsContext* funDefs();

  class  ConstructorTypeContext : public antlr4::ParserRuleContext {
  public:
    ConstructorTypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    TypeListContext *typeList();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ConstructorTypeContext* constructorType();

  class  VarTypeListContext : public antlr4::ParserRuleContext {
  public:
    VarTypeListContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> VAR();
    antlr4::tree::TerminalNode* VAR(size_t i);
    std::vector<TypeContext *> type();
    TypeContext* type(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  VarTypeListContext* varTypeList();

  class  TypeListContext : public antlr4::ParserRuleContext {
  public:
    TypeListContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TypeContext *> type();
    TypeContext* type(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TypeListContext* typeList();

  class  Type0Context : public antlr4::ParserRuleContext {
  public:
    Type0Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Type0Context() : antlr4::ParserRuleContext() { }
    void copyFrom(Type0Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  TypeVarContext : public Type0Context {
  public:
    TypeVarContext(Type0Context *ctx);

    antlr4::tree::TerminalNode *TYPEVAR();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  ParenTypeContext : public Type0Context {
  public:
    ParenTypeContext(Type0Context *ctx);

    TypeContext *type();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  TypeRefContext : public Type0Context {
  public:
    TypeRefContext(Type0Context *ctx);

    antlr4::tree::TerminalNode *ID();
    ParameterListContext *parameterList();
    std::vector<TypeContext *> type();
    TypeContext* type(size_t i);
    Type0Context *type0();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  Type0Context* type0();
  Type0Context* type0(int precedence);
  class  TypeContext : public antlr4::ParserRuleContext {
  public:
    TypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    TypeContext() : antlr4::ParserRuleContext() { }
    void copyFrom(TypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  TupleTypeContext : public TypeContext {
  public:
    TupleTypeContext(TypeContext *ctx);

    std::vector<Type0Context *> type0();
    Type0Context* type0(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  TypeContext* type();

  class  ParameterListContext : public antlr4::ParserRuleContext {
  public:
    ParameterListContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ParameterContext *> parameter();
    ParameterContext* parameter(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ParameterListContext* parameterList();

  class  ParameterContext : public antlr4::ParserRuleContext {
  public:
    ParameterContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    ParameterContext() : antlr4::ParserRuleContext() { }
    void copyFrom(ParameterContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  WildCardParamContext : public ParameterContext {
  public:
    WildCardParamContext(ParameterContext *ctx);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  TypeParamContext : public ParameterContext {
  public:
    TypeParamContext(ParameterContext *ctx);

    TypeContext *type();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  IntParamContext : public ParameterContext {
  public:
    IntParamContext(ParameterContext *ctx);

    antlr4::tree::TerminalNode *INT();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  ParameterContext* parameter();

  class  TypeDefLHSContext : public antlr4::ParserRuleContext {
  public:
    TypeDefLHSContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    std::vector<antlr4::tree::TerminalNode *> TYPEVAR();
    antlr4::tree::TerminalNode* TYPEVAR(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TypeDefLHSContext* typeDefLHS();

  class  TypeDefRHSContext : public antlr4::ParserRuleContext {
  public:
    TypeDefRHSContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    AdtDefContext *adtDef();
    RecordDefContext *recordDef();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TypeDefRHSContext* typeDefRHS();

  class  AdtDefContext : public antlr4::ParserRuleContext {
  public:
    AdtDefContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ConstructorTypeContext *> constructorType();
    ConstructorTypeContext* constructorType(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  AdtDefContext* adtDef();

  class  RecordDefContext : public antlr4::ParserRuleContext {
  public:
    RecordDefContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<RecordEntryDefContext *> recordEntryDef();
    RecordEntryDefContext* recordEntryDef(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  RecordDefContext* recordDef();

  class  RecordEntryDefContext : public antlr4::ParserRuleContext {
  public:
    RecordEntryDefContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    TypeContext *type();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  RecordEntryDefContext* recordEntryDef();

  class  AnnotationContext : public antlr4::ParserRuleContext {
  public:
    AnnotationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  AnnotationContext* annotation();

  class  StmtContext : public antlr4::ParserRuleContext {
  public:
    StmtContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    StmtContext() : antlr4::ParserRuleContext() { }
    void copyFrom(StmtContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  ClauseStmtContext : public StmtContext {
  public:
    ClauseStmtContext(StmtContext *ctx);

    ClauseContext *clause();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  FactStmtContext : public StmtContext {
  public:
    FactStmtContext(StmtContext *ctx);

    FactContext *fact();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  QueryStmtContext : public StmtContext {
  public:
    QueryStmtContext(StmtContext *ctx);

    QueryContext *query();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  StmtContext* stmt();

  class  ClauseContext : public antlr4::ParserRuleContext {
  public:
    FormulogParser::NonEmptyTermListContext *head = nullptr;;
    FormulogParser::NonEmptyTermListContext *body = nullptr;;
    ClauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<NonEmptyTermListContext *> nonEmptyTermList();
    NonEmptyTermListContext* nonEmptyTermList(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ClauseContext* clause();

  class  FactContext : public antlr4::ParserRuleContext {
  public:
    FactContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    TermContext *term();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  FactContext* fact();

  class  QueryContext : public antlr4::ParserRuleContext {
  public:
    QueryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    TermContext *term();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  QueryContext* query();

  class  PredicateContext : public antlr4::ParserRuleContext {
  public:
    PredicateContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    TermArgsContext *termArgs();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  PredicateContext* predicate();

  class  FunctorContext : public antlr4::ParserRuleContext {
  public:
    FunctorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    FunctorContext() : antlr4::ParserRuleContext() { }
    void copyFrom(FunctorContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  IndexedFunctorContext : public FunctorContext {
  public:
    IndexedFunctorContext(FunctorContext *ctx);

    antlr4::Token *id = nullptr;
    ParameterListContext *parameterList();
    TermArgsContext *termArgs();
    antlr4::tree::TerminalNode *ID();
    antlr4::tree::TerminalNode *XID();
    antlr4::tree::TerminalNode *XVAR();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  FunctorContext* functor();

  class  TermArgsContext : public antlr4::ParserRuleContext {
  public:
    TermArgsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TermArgsContext* termArgs();

  class  TermContext : public antlr4::ParserRuleContext {
  public:
    TermContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    TermContext() : antlr4::ParserRuleContext() { }
    void copyFrom(TermContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  QuantifiedFormulaContext : public TermContext {
  public:
    QuantifiedFormulaContext(TermContext *ctx);

    antlr4::Token *quantifier = nullptr;
    FormulogParser::NonEmptyTermListContext *variables = nullptr;
    FormulogParser::NonEmptyTermListContext *pattern = nullptr;
    FormulogParser::TermContext *boundTerm = nullptr;
    std::vector<NonEmptyTermListContext *> nonEmptyTermList();
    NonEmptyTermListContext* nonEmptyTermList(size_t i);
    TermContext *term();
    antlr4::tree::TerminalNode *FORALL();
    antlr4::tree::TerminalNode *EXISTS();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  BinopTermContext : public TermContext {
  public:
    BinopTermContext(TermContext *ctx);

    antlr4::Token *op = nullptr;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    antlr4::tree::TerminalNode *MUL();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *REM();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *LT();
    antlr4::tree::TerminalNode *LTE();
    antlr4::tree::TerminalNode *GT();
    antlr4::tree::TerminalNode *GTE();
    antlr4::tree::TerminalNode *EQ();
    antlr4::tree::TerminalNode *NEQ();
    antlr4::tree::TerminalNode *AMP();
    antlr4::tree::TerminalNode *CARET();
    antlr4::tree::TerminalNode *AMPAMP();
    antlr4::tree::TerminalNode *BARBAR();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  MatchExprContext : public TermContext {
  public:
    MatchExprContext(TermContext *ctx);

    TermContext *term();
    std::vector<MatchClauseContext *> matchClause();
    MatchClauseContext* matchClause(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  FunctorTermContext : public TermContext {
  public:
    FunctorTermContext(TermContext *ctx);

    FunctorContext *functor();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  I32TermContext : public TermContext {
  public:
    I32TermContext(TermContext *ctx);

    antlr4::Token *val = nullptr;
    antlr4::tree::TerminalNode *INT();
    antlr4::tree::TerminalNode *HEX();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  NotFormulaContext : public TermContext {
  public:
    NotFormulaContext(TermContext *ctx);

    antlr4::tree::TerminalNode *NOT();
    TermContext *term();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  LetExprContext : public TermContext {
  public:
    LetExprContext(TermContext *ctx);

    FormulogParser::LetBindContext *lhs = nullptr;
    FormulogParser::TermContext *assign = nullptr;
    FormulogParser::TermContext *body = nullptr;
    LetBindContext *letBind();
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  FloatTermContext : public TermContext {
  public:
    FloatTermContext(TermContext *ctx);

    antlr4::Token *val = nullptr;
    antlr4::tree::TerminalNode *FP32();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  RecordTermContext : public TermContext {
  public:
    RecordTermContext(TermContext *ctx);

    RecordEntriesContext *recordEntries();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  LetFormulaContext : public TermContext {
  public:
    LetFormulaContext(TermContext *ctx);

    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    antlr4::tree::TerminalNode *EQ();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  UnopTermContext : public TermContext {
  public:
    UnopTermContext(TermContext *ctx);

    antlr4::Token *op = nullptr;
    TermContext *term();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *BANG();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  IfExprContext : public TermContext {
  public:
    IfExprContext(TermContext *ctx);

    FormulogParser::TermContext *guard = nullptr;
    FormulogParser::TermContext *thenExpr = nullptr;
    FormulogParser::TermContext *elseExpr = nullptr;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  HoleTermContext : public TermContext {
  public:
    HoleTermContext(TermContext *ctx);

    antlr4::tree::TerminalNode *HOLE();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  ListTermContext : public TermContext {
  public:
    ListTermContext(TermContext *ctx);

    ListContext *list();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  VarTermContext : public TermContext {
  public:
    VarTermContext(TermContext *ctx);

    antlr4::tree::TerminalNode *VAR();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  StringTermContext : public TermContext {
  public:
    StringTermContext(TermContext *ctx);

    antlr4::tree::TerminalNode *QSTRING();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  FormulaTermContext : public TermContext {
  public:
    FormulaTermContext(TermContext *ctx);

    TermContext *term();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  ConsTermContext : public TermContext {
  public:
    ConsTermContext(TermContext *ctx);

    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  TermSymFormulaContext : public TermContext {
  public:
    TermSymFormulaContext(TermContext *ctx);

    TermContext *term();
    TypeContext *type();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  ParensTermContext : public TermContext {
  public:
    ParensTermContext(TermContext *ctx);

    TermContext *term();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  I64TermContext : public TermContext {
  public:
    I64TermContext(TermContext *ctx);

    antlr4::Token *val = nullptr;
    antlr4::tree::TerminalNode *I64();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  IteTermContext : public TermContext {
  public:
    IteTermContext(TermContext *ctx);

    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  FoldTermContext : public TermContext {
  public:
    FoldTermContext(TermContext *ctx);

    antlr4::tree::TerminalNode *ID();
    TermArgsContext *termArgs();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  SpecialFPTermContext : public TermContext {
  public:
    SpecialFPTermContext(TermContext *ctx);

    antlr4::Token *val = nullptr;
    antlr4::tree::TerminalNode *FP32_NAN();
    antlr4::tree::TerminalNode *FP32_POS_INFINITY();
    antlr4::tree::TerminalNode *FP32_NEG_INFINITY();
    antlr4::tree::TerminalNode *FP64_NAN();
    antlr4::tree::TerminalNode *FP64_POS_INFINITY();
    antlr4::tree::TerminalNode *FP64_NEG_INFINITY();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  DoubleTermContext : public TermContext {
  public:
    DoubleTermContext(TermContext *ctx);

    antlr4::Token *val = nullptr;
    antlr4::tree::TerminalNode *FP64();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  LetFunExprContext : public TermContext {
  public:
    LetFunExprContext(TermContext *ctx);

    FormulogParser::TermContext *letFunBody = nullptr;
    FunDefsContext *funDefs();
    TermContext *term();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  BinopFormulaContext : public TermContext {
  public:
    BinopFormulaContext(TermContext *ctx);

    antlr4::Token *op = nullptr;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    antlr4::tree::TerminalNode *FORMULA_EQ();
    antlr4::tree::TerminalNode *AND();
    antlr4::tree::TerminalNode *OR();
    antlr4::tree::TerminalNode *IMP();
    antlr4::tree::TerminalNode *IFF();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  OutermostCtorContext : public TermContext {
  public:
    OutermostCtorContext(TermContext *ctx);

    TermContext *term();
    antlr4::tree::TerminalNode *ISNOT();
    antlr4::tree::TerminalNode *ID();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  TupleTermContext : public TermContext {
  public:
    TupleTermContext(TermContext *ctx);

    TupleContext *tuple();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  class  RecordUpdateTermContext : public TermContext {
  public:
    RecordUpdateTermContext(TermContext *ctx);

    TermContext *term();
    RecordEntriesContext *recordEntries();
    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
  };

  TermContext* term();
  TermContext* term(int precedence);
  class  RecordEntriesContext : public antlr4::ParserRuleContext {
  public:
    RecordEntriesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<RecordEntryContext *> recordEntry();
    RecordEntryContext* recordEntry(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  RecordEntriesContext* recordEntries();

  class  RecordEntryContext : public antlr4::ParserRuleContext {
  public:
    RecordEntryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ID();
    TermContext *term();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  RecordEntryContext* recordEntry();

  class  LetBindContext : public antlr4::ParserRuleContext {
  public:
    LetBindContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  LetBindContext* letBind();

  class  NonEmptyTermListContext : public antlr4::ParserRuleContext {
  public:
    NonEmptyTermListContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  NonEmptyTermListContext* nonEmptyTermList();

  class  ListContext : public antlr4::ParserRuleContext {
  public:
    ListContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ListContext* list();

  class  TupleContext : public antlr4::ParserRuleContext {
  public:
    TupleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TupleContext* tuple();

  class  MatchClauseContext : public antlr4::ParserRuleContext {
  public:
    FormulogParser::PatternsContext *pats = nullptr;;
    FormulogParser::TermContext *rhs = nullptr;;
    MatchClauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PatternsContext *patterns();
    TermContext *term();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  MatchClauseContext* matchClause();

  class  PatternsContext : public antlr4::ParserRuleContext {
  public:
    PatternsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  PatternsContext* patterns();


  virtual bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;
  bool type0Sempred(Type0Context *_localctx, size_t predicateIndex);
  bool termSempred(TermContext *_localctx, size_t predicateIndex);

private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

