
// Generated from Formulog.g4 by ANTLR 4.7.1


#include "FormulogVisitor.h"

#include "FormulogParser.h"


using namespace antlrcpp;
using namespace antlr4;

FormulogParser::FormulogParser(TokenStream *input) : Parser(input) {
  _interpreter = new atn::ParserATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

FormulogParser::~FormulogParser() {
  delete _interpreter;
}

std::string FormulogParser::getGrammarFileName() const {
  return "Formulog.g4";
}

const std::vector<std::string>& FormulogParser::getRuleNames() const {
  return _ruleNames;
}

dfa::Vocabulary& FormulogParser::getVocabulary() const {
  return _vocabulary;
}


//----------------- ProgContext ------------------------------------------------------------------

FormulogParser::ProgContext::ProgContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::ProgContext::EOF() {
  return getToken(FormulogParser::EOF, 0);
}

std::vector<FormulogParser::MetadataContext *> FormulogParser::ProgContext::metadata() {
  return getRuleContexts<FormulogParser::MetadataContext>();
}

FormulogParser::MetadataContext* FormulogParser::ProgContext::metadata(size_t i) {
  return getRuleContext<FormulogParser::MetadataContext>(i);
}

std::vector<FormulogParser::StmtContext *> FormulogParser::ProgContext::stmt() {
  return getRuleContexts<FormulogParser::StmtContext>();
}

FormulogParser::StmtContext* FormulogParser::ProgContext::stmt(size_t i) {
  return getRuleContext<FormulogParser::StmtContext>(i);
}


size_t FormulogParser::ProgContext::getRuleIndex() const {
  return FormulogParser::RuleProg;
}

antlrcpp::Any FormulogParser::ProgContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitProg(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::ProgContext* FormulogParser::prog() {
  ProgContext *_localctx = _tracker.createInstance<ProgContext>(_ctx, getState());
  enterRule(_localctx, 0, FormulogParser::RuleProg);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(74);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << FormulogParser::T__1)
      | (1ULL << FormulogParser::T__3)
      | (1ULL << FormulogParser::T__4)
      | (1ULL << FormulogParser::T__7)
      | (1ULL << FormulogParser::T__10)
      | (1ULL << FormulogParser::T__14)
      | (1ULL << FormulogParser::T__17)
      | (1ULL << FormulogParser::T__18)
      | (1ULL << FormulogParser::T__19)
      | (1ULL << FormulogParser::T__22)
      | (1ULL << FormulogParser::T__23)
      | (1ULL << FormulogParser::T__24)
      | (1ULL << FormulogParser::T__26)
      | (1ULL << FormulogParser::T__29)
      | (1ULL << FormulogParser::T__31)
      | (1ULL << FormulogParser::T__32)
      | (1ULL << FormulogParser::NOT)
      | (1ULL << FormulogParser::INPUT)
      | (1ULL << FormulogParser::OUTPUT)
      | (1ULL << FormulogParser::FP32_NAN)
      | (1ULL << FormulogParser::FP32_POS_INFINITY)
      | (1ULL << FormulogParser::FP32_NEG_INFINITY)
      | (1ULL << FormulogParser::FP64_NAN)
      | (1ULL << FormulogParser::FP64_POS_INFINITY)
      | (1ULL << FormulogParser::FP64_NEG_INFINITY)
      | (1ULL << FormulogParser::XVAR)
      | (1ULL << FormulogParser::VAR)
      | (1ULL << FormulogParser::INT)
      | (1ULL << FormulogParser::HEX)
      | (1ULL << FormulogParser::FP32)
      | (1ULL << FormulogParser::FP64)
      | (1ULL << FormulogParser::I64))) != 0) || ((((_la - 65) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 65)) & ((1ULL << (FormulogParser::MINUS - 65))
      | (1ULL << (FormulogParser::BANG - 65))
      | (1ULL << (FormulogParser::FORALL - 65))
      | (1ULL << (FormulogParser::EXISTS - 65))
      | (1ULL << (FormulogParser::HOLE - 65))
      | (1ULL << (FormulogParser::XID - 65))
      | (1ULL << (FormulogParser::ID - 65))
      | (1ULL << (FormulogParser::QSTRING - 65)))) != 0)) {
      setState(72);
      _errHandler->sync(this);
      switch (_input->LA(1)) {
        case FormulogParser::T__1:
        case FormulogParser::T__3:
        case FormulogParser::T__4:
        case FormulogParser::T__17:
        case FormulogParser::INPUT:
        case FormulogParser::OUTPUT: {
          setState(70);
          metadata();
          break;
        }

        case FormulogParser::T__7:
        case FormulogParser::T__10:
        case FormulogParser::T__14:
        case FormulogParser::T__18:
        case FormulogParser::T__19:
        case FormulogParser::T__22:
        case FormulogParser::T__23:
        case FormulogParser::T__24:
        case FormulogParser::T__26:
        case FormulogParser::T__29:
        case FormulogParser::T__31:
        case FormulogParser::T__32:
        case FormulogParser::NOT:
        case FormulogParser::FP32_NAN:
        case FormulogParser::FP32_POS_INFINITY:
        case FormulogParser::FP32_NEG_INFINITY:
        case FormulogParser::FP64_NAN:
        case FormulogParser::FP64_POS_INFINITY:
        case FormulogParser::FP64_NEG_INFINITY:
        case FormulogParser::XVAR:
        case FormulogParser::VAR:
        case FormulogParser::INT:
        case FormulogParser::HEX:
        case FormulogParser::FP32:
        case FormulogParser::FP64:
        case FormulogParser::I64:
        case FormulogParser::MINUS:
        case FormulogParser::BANG:
        case FormulogParser::FORALL:
        case FormulogParser::EXISTS:
        case FormulogParser::HOLE:
        case FormulogParser::XID:
        case FormulogParser::ID:
        case FormulogParser::QSTRING: {
          setState(71);
          stmt();
          break;
        }

      default:
        throw NoViableAltException(this);
      }
      setState(76);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(77);
    match(FormulogParser::EOF);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TsvFileContext ------------------------------------------------------------------

FormulogParser::TsvFileContext::TsvFileContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::TsvFileContext::EOF() {
  return getToken(FormulogParser::EOF, 0);
}

std::vector<FormulogParser::TabSeparatedTermLineContext *> FormulogParser::TsvFileContext::tabSeparatedTermLine() {
  return getRuleContexts<FormulogParser::TabSeparatedTermLineContext>();
}

FormulogParser::TabSeparatedTermLineContext* FormulogParser::TsvFileContext::tabSeparatedTermLine(size_t i) {
  return getRuleContext<FormulogParser::TabSeparatedTermLineContext>(i);
}


size_t FormulogParser::TsvFileContext::getRuleIndex() const {
  return FormulogParser::RuleTsvFile;
}

antlrcpp::Any FormulogParser::TsvFileContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTsvFile(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TsvFileContext* FormulogParser::tsvFile() {
  TsvFileContext *_localctx = _tracker.createInstance<TsvFileContext>(_ctx, getState());
  enterRule(_localctx, 2, FormulogParser::RuleTsvFile);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(82);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << FormulogParser::T__7)
      | (1ULL << FormulogParser::T__10)
      | (1ULL << FormulogParser::T__14)
      | (1ULL << FormulogParser::T__19)
      | (1ULL << FormulogParser::T__22)
      | (1ULL << FormulogParser::T__23)
      | (1ULL << FormulogParser::T__24)
      | (1ULL << FormulogParser::T__26)
      | (1ULL << FormulogParser::T__29)
      | (1ULL << FormulogParser::T__31)
      | (1ULL << FormulogParser::T__32)
      | (1ULL << FormulogParser::NOT)
      | (1ULL << FormulogParser::FP32_NAN)
      | (1ULL << FormulogParser::FP32_POS_INFINITY)
      | (1ULL << FormulogParser::FP32_NEG_INFINITY)
      | (1ULL << FormulogParser::FP64_NAN)
      | (1ULL << FormulogParser::FP64_POS_INFINITY)
      | (1ULL << FormulogParser::FP64_NEG_INFINITY)
      | (1ULL << FormulogParser::XVAR)
      | (1ULL << FormulogParser::VAR)
      | (1ULL << FormulogParser::INT)
      | (1ULL << FormulogParser::HEX)
      | (1ULL << FormulogParser::FP32)
      | (1ULL << FormulogParser::FP64)
      | (1ULL << FormulogParser::I64))) != 0) || ((((_la - 65) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 65)) & ((1ULL << (FormulogParser::MINUS - 65))
      | (1ULL << (FormulogParser::BANG - 65))
      | (1ULL << (FormulogParser::FORALL - 65))
      | (1ULL << (FormulogParser::EXISTS - 65))
      | (1ULL << (FormulogParser::HOLE - 65))
      | (1ULL << (FormulogParser::NEWLINE - 65))
      | (1ULL << (FormulogParser::XID - 65))
      | (1ULL << (FormulogParser::ID - 65))
      | (1ULL << (FormulogParser::QSTRING - 65)))) != 0)) {
      setState(79);
      tabSeparatedTermLine();
      setState(84);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(85);
    match(FormulogParser::EOF);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TabSeparatedTermLineContext ------------------------------------------------------------------

FormulogParser::TabSeparatedTermLineContext::TabSeparatedTermLineContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::TabSeparatedTermLineContext::NEWLINE() {
  return getToken(FormulogParser::NEWLINE, 0);
}

std::vector<FormulogParser::TermContext *> FormulogParser::TabSeparatedTermLineContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::TabSeparatedTermLineContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

std::vector<tree::TerminalNode *> FormulogParser::TabSeparatedTermLineContext::TAB() {
  return getTokens(FormulogParser::TAB);
}

tree::TerminalNode* FormulogParser::TabSeparatedTermLineContext::TAB(size_t i) {
  return getToken(FormulogParser::TAB, i);
}


size_t FormulogParser::TabSeparatedTermLineContext::getRuleIndex() const {
  return FormulogParser::RuleTabSeparatedTermLine;
}

antlrcpp::Any FormulogParser::TabSeparatedTermLineContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTabSeparatedTermLine(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TabSeparatedTermLineContext* FormulogParser::tabSeparatedTermLine() {
  TabSeparatedTermLineContext *_localctx = _tracker.createInstance<TabSeparatedTermLineContext>(_ctx, getState());
  enterRule(_localctx, 4, FormulogParser::RuleTabSeparatedTermLine);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(95);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << FormulogParser::T__7)
      | (1ULL << FormulogParser::T__10)
      | (1ULL << FormulogParser::T__14)
      | (1ULL << FormulogParser::T__19)
      | (1ULL << FormulogParser::T__22)
      | (1ULL << FormulogParser::T__23)
      | (1ULL << FormulogParser::T__24)
      | (1ULL << FormulogParser::T__26)
      | (1ULL << FormulogParser::T__29)
      | (1ULL << FormulogParser::T__31)
      | (1ULL << FormulogParser::T__32)
      | (1ULL << FormulogParser::NOT)
      | (1ULL << FormulogParser::FP32_NAN)
      | (1ULL << FormulogParser::FP32_POS_INFINITY)
      | (1ULL << FormulogParser::FP32_NEG_INFINITY)
      | (1ULL << FormulogParser::FP64_NAN)
      | (1ULL << FormulogParser::FP64_POS_INFINITY)
      | (1ULL << FormulogParser::FP64_NEG_INFINITY)
      | (1ULL << FormulogParser::XVAR)
      | (1ULL << FormulogParser::VAR)
      | (1ULL << FormulogParser::INT)
      | (1ULL << FormulogParser::HEX)
      | (1ULL << FormulogParser::FP32)
      | (1ULL << FormulogParser::FP64)
      | (1ULL << FormulogParser::I64))) != 0) || ((((_la - 65) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 65)) & ((1ULL << (FormulogParser::MINUS - 65))
      | (1ULL << (FormulogParser::BANG - 65))
      | (1ULL << (FormulogParser::FORALL - 65))
      | (1ULL << (FormulogParser::EXISTS - 65))
      | (1ULL << (FormulogParser::HOLE - 65))
      | (1ULL << (FormulogParser::XID - 65))
      | (1ULL << (FormulogParser::ID - 65))
      | (1ULL << (FormulogParser::QSTRING - 65)))) != 0)) {
      setState(87);
      term(0);
      setState(92);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::TAB) {
        setState(88);
        match(FormulogParser::TAB);
        setState(89);
        term(0);
        setState(94);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
    }
    setState(97);
    match(FormulogParser::NEWLINE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- MetadataContext ------------------------------------------------------------------

FormulogParser::MetadataContext::MetadataContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::MetadataContext::getRuleIndex() const {
  return FormulogParser::RuleMetadata;
}

void FormulogParser::MetadataContext::copyFrom(MetadataContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- UninterpSortDeclContext ------------------------------------------------------------------

FormulogParser::TypeDefLHSContext* FormulogParser::UninterpSortDeclContext::typeDefLHS() {
  return getRuleContext<FormulogParser::TypeDefLHSContext>(0);
}

FormulogParser::UninterpSortDeclContext::UninterpSortDeclContext(MetadataContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::UninterpSortDeclContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitUninterpSortDecl(this);
  else
    return visitor->visitChildren(this);
}
//----------------- RelDeclContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::RelDeclContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::TypeListContext* FormulogParser::RelDeclContext::typeList() {
  return getRuleContext<FormulogParser::TypeListContext>(0);
}

tree::TerminalNode* FormulogParser::RelDeclContext::INPUT() {
  return getToken(FormulogParser::INPUT, 0);
}

tree::TerminalNode* FormulogParser::RelDeclContext::OUTPUT() {
  return getToken(FormulogParser::OUTPUT, 0);
}

std::vector<FormulogParser::AnnotationContext *> FormulogParser::RelDeclContext::annotation() {
  return getRuleContexts<FormulogParser::AnnotationContext>();
}

FormulogParser::AnnotationContext* FormulogParser::RelDeclContext::annotation(size_t i) {
  return getRuleContext<FormulogParser::AnnotationContext>(i);
}

FormulogParser::RelDeclContext::RelDeclContext(MetadataContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::RelDeclContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRelDecl(this);
  else
    return visitor->visitChildren(this);
}
//----------------- UninterpFunDeclContext ------------------------------------------------------------------

FormulogParser::ConstructorTypeContext* FormulogParser::UninterpFunDeclContext::constructorType() {
  return getRuleContext<FormulogParser::ConstructorTypeContext>(0);
}

FormulogParser::TypeContext* FormulogParser::UninterpFunDeclContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}

FormulogParser::UninterpFunDeclContext::UninterpFunDeclContext(MetadataContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::UninterpFunDeclContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitUninterpFunDecl(this);
  else
    return visitor->visitChildren(this);
}
//----------------- FunDeclContext ------------------------------------------------------------------

FormulogParser::FunDefsContext* FormulogParser::FunDeclContext::funDefs() {
  return getRuleContext<FormulogParser::FunDefsContext>(0);
}

FormulogParser::FunDeclContext::FunDeclContext(MetadataContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::FunDeclContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFunDecl(this);
  else
    return visitor->visitChildren(this);
}
//----------------- TypeAliasContext ------------------------------------------------------------------

FormulogParser::TypeDefLHSContext* FormulogParser::TypeAliasContext::typeDefLHS() {
  return getRuleContext<FormulogParser::TypeDefLHSContext>(0);
}

tree::TerminalNode* FormulogParser::TypeAliasContext::EQ() {
  return getToken(FormulogParser::EQ, 0);
}

FormulogParser::TypeContext* FormulogParser::TypeAliasContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}

FormulogParser::TypeAliasContext::TypeAliasContext(MetadataContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TypeAliasContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeAlias(this);
  else
    return visitor->visitChildren(this);
}
//----------------- TypeDeclContext ------------------------------------------------------------------

std::vector<FormulogParser::TypeDefLHSContext *> FormulogParser::TypeDeclContext::typeDefLHS() {
  return getRuleContexts<FormulogParser::TypeDefLHSContext>();
}

FormulogParser::TypeDefLHSContext* FormulogParser::TypeDeclContext::typeDefLHS(size_t i) {
  return getRuleContext<FormulogParser::TypeDefLHSContext>(i);
}

std::vector<tree::TerminalNode *> FormulogParser::TypeDeclContext::EQ() {
  return getTokens(FormulogParser::EQ);
}

tree::TerminalNode* FormulogParser::TypeDeclContext::EQ(size_t i) {
  return getToken(FormulogParser::EQ, i);
}

std::vector<FormulogParser::TypeDefRHSContext *> FormulogParser::TypeDeclContext::typeDefRHS() {
  return getRuleContexts<FormulogParser::TypeDefRHSContext>();
}

FormulogParser::TypeDefRHSContext* FormulogParser::TypeDeclContext::typeDefRHS(size_t i) {
  return getRuleContext<FormulogParser::TypeDefRHSContext>(i);
}

FormulogParser::TypeDeclContext::TypeDeclContext(MetadataContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TypeDeclContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeDecl(this);
  else
    return visitor->visitChildren(this);
}
FormulogParser::MetadataContext* FormulogParser::metadata() {
  MetadataContext *_localctx = _tracker.createInstance<MetadataContext>(_ctx, getState());
  enterRule(_localctx, 6, FormulogParser::RuleMetadata);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(153);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx)) {
    case 1: {
      _localctx = dynamic_cast<MetadataContext *>(_tracker.createInstance<FormulogParser::FunDeclContext>(_localctx));
      enterOuterAlt(_localctx, 1);
      setState(99);
      funDefs();
      setState(101);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__0) {
        setState(100);
        match(FormulogParser::T__0);
      }
      break;
    }

    case 2: {
      _localctx = dynamic_cast<MetadataContext *>(_tracker.createInstance<FormulogParser::RelDeclContext>(_localctx));
      enterOuterAlt(_localctx, 2);
      setState(106);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__17) {
        setState(103);
        annotation();
        setState(108);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(109);
      dynamic_cast<RelDeclContext *>(_localctx)->relType = _input->LT(1);
      _la = _input->LA(1);
      if (!(_la == FormulogParser::INPUT

      || _la == FormulogParser::OUTPUT)) {
        dynamic_cast<RelDeclContext *>(_localctx)->relType = _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(110);
      match(FormulogParser::ID);
      setState(111);
      typeList();
      setState(113);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__0) {
        setState(112);
        match(FormulogParser::T__0);
      }
      break;
    }

    case 3: {
      _localctx = dynamic_cast<MetadataContext *>(_tracker.createInstance<FormulogParser::TypeAliasContext>(_localctx));
      enterOuterAlt(_localctx, 3);
      setState(115);
      match(FormulogParser::T__1);
      setState(116);
      typeDefLHS();
      setState(117);
      match(FormulogParser::EQ);
      setState(118);
      type();
      setState(120);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__0) {
        setState(119);
        match(FormulogParser::T__0);
      }
      break;
    }

    case 4: {
      _localctx = dynamic_cast<MetadataContext *>(_tracker.createInstance<FormulogParser::TypeDeclContext>(_localctx));
      enterOuterAlt(_localctx, 4);
      setState(122);
      match(FormulogParser::T__1);
      setState(123);
      typeDefLHS();
      setState(124);
      match(FormulogParser::EQ);
      setState(125);
      typeDefRHS();
      setState(133);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__2) {
        setState(126);
        match(FormulogParser::T__2);
        setState(127);
        typeDefLHS();
        setState(128);
        match(FormulogParser::EQ);
        setState(129);
        typeDefRHS();
        setState(135);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(137);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__0) {
        setState(136);
        match(FormulogParser::T__0);
      }
      break;
    }

    case 5: {
      _localctx = dynamic_cast<MetadataContext *>(_tracker.createInstance<FormulogParser::UninterpFunDeclContext>(_localctx));
      enterOuterAlt(_localctx, 5);
      setState(139);
      match(FormulogParser::T__3);
      setState(140);
      match(FormulogParser::T__4);
      setState(141);
      constructorType();
      setState(142);
      match(FormulogParser::T__5);
      setState(143);
      type();
      setState(145);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__0) {
        setState(144);
        match(FormulogParser::T__0);
      }
      break;
    }

    case 6: {
      _localctx = dynamic_cast<MetadataContext *>(_tracker.createInstance<FormulogParser::UninterpSortDeclContext>(_localctx));
      enterOuterAlt(_localctx, 6);
      setState(147);
      match(FormulogParser::T__3);
      setState(148);
      match(FormulogParser::T__6);
      setState(149);
      typeDefLHS();
      setState(151);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__0) {
        setState(150);
        match(FormulogParser::T__0);
      }
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- FunDefLHSContext ------------------------------------------------------------------

FormulogParser::FunDefLHSContext::FunDefLHSContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::FunDefLHSContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::VarTypeListContext* FormulogParser::FunDefLHSContext::varTypeList() {
  return getRuleContext<FormulogParser::VarTypeListContext>(0);
}

FormulogParser::TypeContext* FormulogParser::FunDefLHSContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}


size_t FormulogParser::FunDefLHSContext::getRuleIndex() const {
  return FormulogParser::RuleFunDefLHS;
}

antlrcpp::Any FormulogParser::FunDefLHSContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFunDefLHS(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::FunDefLHSContext* FormulogParser::funDefLHS() {
  FunDefLHSContext *_localctx = _tracker.createInstance<FunDefLHSContext>(_ctx, getState());
  enterRule(_localctx, 8, FormulogParser::RuleFunDefLHS);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(155);
    match(FormulogParser::ID);
    setState(156);
    dynamic_cast<FunDefLHSContext *>(_localctx)->args = varTypeList();
    setState(157);
    match(FormulogParser::T__5);
    setState(158);
    dynamic_cast<FunDefLHSContext *>(_localctx)->retType = type();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- FunDefsContext ------------------------------------------------------------------

FormulogParser::FunDefsContext::FunDefsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::FunDefLHSContext *> FormulogParser::FunDefsContext::funDefLHS() {
  return getRuleContexts<FormulogParser::FunDefLHSContext>();
}

FormulogParser::FunDefLHSContext* FormulogParser::FunDefsContext::funDefLHS(size_t i) {
  return getRuleContext<FormulogParser::FunDefLHSContext>(i);
}

std::vector<tree::TerminalNode *> FormulogParser::FunDefsContext::EQ() {
  return getTokens(FormulogParser::EQ);
}

tree::TerminalNode* FormulogParser::FunDefsContext::EQ(size_t i) {
  return getToken(FormulogParser::EQ, i);
}

std::vector<FormulogParser::TermContext *> FormulogParser::FunDefsContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::FunDefsContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::FunDefsContext::getRuleIndex() const {
  return FormulogParser::RuleFunDefs;
}

antlrcpp::Any FormulogParser::FunDefsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFunDefs(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::FunDefsContext* FormulogParser::funDefs() {
  FunDefsContext *_localctx = _tracker.createInstance<FunDefsContext>(_ctx, getState());
  enterRule(_localctx, 10, FormulogParser::RuleFunDefs);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(160);
    match(FormulogParser::T__4);
    setState(161);
    funDefLHS();
    setState(162);
    match(FormulogParser::EQ);
    setState(163);
    term(0);
    setState(171);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == FormulogParser::T__2) {
      setState(164);
      match(FormulogParser::T__2);
      setState(165);
      funDefLHS();
      setState(166);
      match(FormulogParser::EQ);
      setState(167);
      term(0);
      setState(173);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ConstructorTypeContext ------------------------------------------------------------------

FormulogParser::ConstructorTypeContext::ConstructorTypeContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::ConstructorTypeContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::TypeListContext* FormulogParser::ConstructorTypeContext::typeList() {
  return getRuleContext<FormulogParser::TypeListContext>(0);
}


size_t FormulogParser::ConstructorTypeContext::getRuleIndex() const {
  return FormulogParser::RuleConstructorType;
}

antlrcpp::Any FormulogParser::ConstructorTypeContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitConstructorType(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::ConstructorTypeContext* FormulogParser::constructorType() {
  ConstructorTypeContext *_localctx = _tracker.createInstance<ConstructorTypeContext>(_ctx, getState());
  enterRule(_localctx, 12, FormulogParser::RuleConstructorType);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(174);
    match(FormulogParser::ID);
    setState(175);
    typeList();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- VarTypeListContext ------------------------------------------------------------------

FormulogParser::VarTypeListContext::VarTypeListContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> FormulogParser::VarTypeListContext::VAR() {
  return getTokens(FormulogParser::VAR);
}

tree::TerminalNode* FormulogParser::VarTypeListContext::VAR(size_t i) {
  return getToken(FormulogParser::VAR, i);
}

std::vector<FormulogParser::TypeContext *> FormulogParser::VarTypeListContext::type() {
  return getRuleContexts<FormulogParser::TypeContext>();
}

FormulogParser::TypeContext* FormulogParser::VarTypeListContext::type(size_t i) {
  return getRuleContext<FormulogParser::TypeContext>(i);
}


size_t FormulogParser::VarTypeListContext::getRuleIndex() const {
  return FormulogParser::RuleVarTypeList;
}

antlrcpp::Any FormulogParser::VarTypeListContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitVarTypeList(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::VarTypeListContext* FormulogParser::varTypeList() {
  VarTypeListContext *_localctx = _tracker.createInstance<VarTypeListContext>(_ctx, getState());
  enterRule(_localctx, 14, FormulogParser::RuleVarTypeList);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(193);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case FormulogParser::T__7: {
        enterOuterAlt(_localctx, 1);
        setState(177);
        match(FormulogParser::T__7);
        setState(178);
        match(FormulogParser::VAR);
        setState(179);
        match(FormulogParser::T__5);
        setState(180);
        type();
        setState(187);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == FormulogParser::T__8) {
          setState(181);
          match(FormulogParser::T__8);
          setState(182);
          match(FormulogParser::VAR);
          setState(183);
          match(FormulogParser::T__5);
          setState(184);
          type();
          setState(189);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(190);
        match(FormulogParser::T__9);
        break;
      }

      case FormulogParser::T__5: {
        enterOuterAlt(_localctx, 2);

        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TypeListContext ------------------------------------------------------------------

FormulogParser::TypeListContext::TypeListContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TypeContext *> FormulogParser::TypeListContext::type() {
  return getRuleContexts<FormulogParser::TypeContext>();
}

FormulogParser::TypeContext* FormulogParser::TypeListContext::type(size_t i) {
  return getRuleContext<FormulogParser::TypeContext>(i);
}


size_t FormulogParser::TypeListContext::getRuleIndex() const {
  return FormulogParser::RuleTypeList;
}

antlrcpp::Any FormulogParser::TypeListContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeList(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TypeListContext* FormulogParser::typeList() {
  TypeListContext *_localctx = _tracker.createInstance<TypeListContext>(_ctx, getState());
  enterRule(_localctx, 16, FormulogParser::RuleTypeList);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(207);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 18, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(195);
      match(FormulogParser::T__7);
      setState(196);
      type();
      setState(201);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__8) {
        setState(197);
        match(FormulogParser::T__8);
        setState(198);
        type();
        setState(203);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(204);
      match(FormulogParser::T__9);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);

      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Type0Context ------------------------------------------------------------------

FormulogParser::Type0Context::Type0Context(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::Type0Context::getRuleIndex() const {
  return FormulogParser::RuleType0;
}

void FormulogParser::Type0Context::copyFrom(Type0Context *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- TypeVarContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::TypeVarContext::TYPEVAR() {
  return getToken(FormulogParser::TYPEVAR, 0);
}

FormulogParser::TypeVarContext::TypeVarContext(Type0Context *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TypeVarContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeVar(this);
  else
    return visitor->visitChildren(this);
}
//----------------- ParenTypeContext ------------------------------------------------------------------

FormulogParser::TypeContext* FormulogParser::ParenTypeContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}

FormulogParser::ParenTypeContext::ParenTypeContext(Type0Context *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::ParenTypeContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitParenType(this);
  else
    return visitor->visitChildren(this);
}
//----------------- TypeRefContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::TypeRefContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::ParameterListContext* FormulogParser::TypeRefContext::parameterList() {
  return getRuleContext<FormulogParser::ParameterListContext>(0);
}

std::vector<FormulogParser::TypeContext *> FormulogParser::TypeRefContext::type() {
  return getRuleContexts<FormulogParser::TypeContext>();
}

FormulogParser::TypeContext* FormulogParser::TypeRefContext::type(size_t i) {
  return getRuleContext<FormulogParser::TypeContext>(i);
}

FormulogParser::Type0Context* FormulogParser::TypeRefContext::type0() {
  return getRuleContext<FormulogParser::Type0Context>(0);
}

FormulogParser::TypeRefContext::TypeRefContext(Type0Context *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TypeRefContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeRef(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::Type0Context* FormulogParser::type0() {
   return type0(0);
}

FormulogParser::Type0Context* FormulogParser::type0(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  FormulogParser::Type0Context *_localctx = _tracker.createInstance<Type0Context>(_ctx, parentState);
  FormulogParser::Type0Context *previousContext = _localctx;
  size_t startState = 18;
  enterRecursionRule(_localctx, 18, FormulogParser::RuleType0, precedence);

    size_t _la = 0;

  auto onExit = finally([=] {
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(230);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 21, _ctx)) {
    case 1: {
      _localctx = _tracker.createInstance<ParenTypeContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;

      setState(210);
      match(FormulogParser::T__7);
      setState(211);
      type();
      setState(212);
      match(FormulogParser::T__9);
      break;
    }

    case 2: {
      _localctx = _tracker.createInstance<TypeVarContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(214);
      match(FormulogParser::TYPEVAR);
      break;
    }

    case 3: {
      _localctx = _tracker.createInstance<TypeRefContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(226);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__7) {
        setState(215);
        match(FormulogParser::T__7);
        setState(216);
        type();
        setState(221);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == FormulogParser::T__8) {
          setState(217);
          match(FormulogParser::T__8);
          setState(218);
          type();
          setState(223);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(224);
        match(FormulogParser::T__9);
      }
      setState(228);
      match(FormulogParser::ID);
      setState(229);
      parameterList();
      break;
    }

    }
    _ctx->stop = _input->LT(-1);
    setState(237);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 22, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        auto newContext = _tracker.createInstance<TypeRefContext>(_tracker.createInstance<Type0Context>(parentContext, parentState));
        _localctx = newContext;
        pushNewRecursionContext(newContext, startState, RuleType0);
        setState(232);

        if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
        setState(233);
        match(FormulogParser::ID);
        setState(234);
        parameterList(); 
      }
      setState(239);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 22, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- TypeContext ------------------------------------------------------------------

FormulogParser::TypeContext::TypeContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::TypeContext::getRuleIndex() const {
  return FormulogParser::RuleType;
}

void FormulogParser::TypeContext::copyFrom(TypeContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- TupleTypeContext ------------------------------------------------------------------

std::vector<FormulogParser::Type0Context *> FormulogParser::TupleTypeContext::type0() {
  return getRuleContexts<FormulogParser::Type0Context>();
}

FormulogParser::Type0Context* FormulogParser::TupleTypeContext::type0(size_t i) {
  return getRuleContext<FormulogParser::Type0Context>(i);
}

FormulogParser::TupleTypeContext::TupleTypeContext(TypeContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TupleTypeContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTupleType(this);
  else
    return visitor->visitChildren(this);
}
FormulogParser::TypeContext* FormulogParser::type() {
  TypeContext *_localctx = _tracker.createInstance<TypeContext>(_ctx, getState());
  enterRule(_localctx, 20, FormulogParser::RuleType);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    _localctx = dynamic_cast<TypeContext *>(_tracker.createInstance<FormulogParser::TupleTypeContext>(_localctx));
    enterOuterAlt(_localctx, 1);
    setState(240);
    type0(0);
    setState(245);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == FormulogParser::MUL) {
      setState(241);
      match(FormulogParser::MUL);
      setState(242);
      type0(0);
      setState(247);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ParameterListContext ------------------------------------------------------------------

FormulogParser::ParameterListContext::ParameterListContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::ParameterContext *> FormulogParser::ParameterListContext::parameter() {
  return getRuleContexts<FormulogParser::ParameterContext>();
}

FormulogParser::ParameterContext* FormulogParser::ParameterListContext::parameter(size_t i) {
  return getRuleContext<FormulogParser::ParameterContext>(i);
}


size_t FormulogParser::ParameterListContext::getRuleIndex() const {
  return FormulogParser::RuleParameterList;
}

antlrcpp::Any FormulogParser::ParameterListContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitParameterList(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::ParameterListContext* FormulogParser::parameterList() {
  ParameterListContext *_localctx = _tracker.createInstance<ParameterListContext>(_ctx, getState());
  enterRule(_localctx, 22, FormulogParser::RuleParameterList);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(260);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 25, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(248);
      match(FormulogParser::T__10);
      setState(249);
      parameter();
      setState(254);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__8) {
        setState(250);
        match(FormulogParser::T__8);
        setState(251);
        parameter();
        setState(256);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(257);
      match(FormulogParser::T__11);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);

      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ParameterContext ------------------------------------------------------------------

FormulogParser::ParameterContext::ParameterContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::ParameterContext::getRuleIndex() const {
  return FormulogParser::RuleParameter;
}

void FormulogParser::ParameterContext::copyFrom(ParameterContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- WildCardParamContext ------------------------------------------------------------------

FormulogParser::WildCardParamContext::WildCardParamContext(ParameterContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::WildCardParamContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitWildCardParam(this);
  else
    return visitor->visitChildren(this);
}
//----------------- TypeParamContext ------------------------------------------------------------------

FormulogParser::TypeContext* FormulogParser::TypeParamContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}

FormulogParser::TypeParamContext::TypeParamContext(ParameterContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TypeParamContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeParam(this);
  else
    return visitor->visitChildren(this);
}
//----------------- IntParamContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::IntParamContext::INT() {
  return getToken(FormulogParser::INT, 0);
}

FormulogParser::IntParamContext::IntParamContext(ParameterContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::IntParamContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitIntParam(this);
  else
    return visitor->visitChildren(this);
}
FormulogParser::ParameterContext* FormulogParser::parameter() {
  ParameterContext *_localctx = _tracker.createInstance<ParameterContext>(_ctx, getState());
  enterRule(_localctx, 24, FormulogParser::RuleParameter);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(265);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case FormulogParser::T__12: {
        _localctx = dynamic_cast<ParameterContext *>(_tracker.createInstance<FormulogParser::WildCardParamContext>(_localctx));
        enterOuterAlt(_localctx, 1);
        setState(262);
        match(FormulogParser::T__12);
        break;
      }

      case FormulogParser::T__7:
      case FormulogParser::TYPEVAR:
      case FormulogParser::ID: {
        _localctx = dynamic_cast<ParameterContext *>(_tracker.createInstance<FormulogParser::TypeParamContext>(_localctx));
        enterOuterAlt(_localctx, 2);
        setState(263);
        type();
        break;
      }

      case FormulogParser::INT: {
        _localctx = dynamic_cast<ParameterContext *>(_tracker.createInstance<FormulogParser::IntParamContext>(_localctx));
        enterOuterAlt(_localctx, 3);
        setState(264);
        match(FormulogParser::INT);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TypeDefLHSContext ------------------------------------------------------------------

FormulogParser::TypeDefLHSContext::TypeDefLHSContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::TypeDefLHSContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

std::vector<tree::TerminalNode *> FormulogParser::TypeDefLHSContext::TYPEVAR() {
  return getTokens(FormulogParser::TYPEVAR);
}

tree::TerminalNode* FormulogParser::TypeDefLHSContext::TYPEVAR(size_t i) {
  return getToken(FormulogParser::TYPEVAR, i);
}


size_t FormulogParser::TypeDefLHSContext::getRuleIndex() const {
  return FormulogParser::RuleTypeDefLHS;
}

antlrcpp::Any FormulogParser::TypeDefLHSContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeDefLHS(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TypeDefLHSContext* FormulogParser::typeDefLHS() {
  TypeDefLHSContext *_localctx = _tracker.createInstance<TypeDefLHSContext>(_ctx, getState());
  enterRule(_localctx, 26, FormulogParser::RuleTypeDefLHS);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(278);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case FormulogParser::TYPEVAR: {
        setState(267);
        match(FormulogParser::TYPEVAR);
        break;
      }

      case FormulogParser::T__7: {
        setState(268);
        match(FormulogParser::T__7);
        setState(269);
        match(FormulogParser::TYPEVAR);
        setState(274);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == FormulogParser::T__8) {
          setState(270);
          match(FormulogParser::T__8);
          setState(271);
          match(FormulogParser::TYPEVAR);
          setState(276);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(277);
        match(FormulogParser::T__9);
        break;
      }

      case FormulogParser::ID: {
        break;
      }

    default:
      break;
    }
    setState(280);
    match(FormulogParser::ID);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TypeDefRHSContext ------------------------------------------------------------------

FormulogParser::TypeDefRHSContext::TypeDefRHSContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

FormulogParser::AdtDefContext* FormulogParser::TypeDefRHSContext::adtDef() {
  return getRuleContext<FormulogParser::AdtDefContext>(0);
}

FormulogParser::RecordDefContext* FormulogParser::TypeDefRHSContext::recordDef() {
  return getRuleContext<FormulogParser::RecordDefContext>(0);
}


size_t FormulogParser::TypeDefRHSContext::getRuleIndex() const {
  return FormulogParser::RuleTypeDefRHS;
}

antlrcpp::Any FormulogParser::TypeDefRHSContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTypeDefRHS(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TypeDefRHSContext* FormulogParser::typeDefRHS() {
  TypeDefRHSContext *_localctx = _tracker.createInstance<TypeDefRHSContext>(_ctx, getState());
  enterRule(_localctx, 28, FormulogParser::RuleTypeDefRHS);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(284);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 29, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(282);
      adtDef();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(283);
      recordDef();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- AdtDefContext ------------------------------------------------------------------

FormulogParser::AdtDefContext::AdtDefContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::ConstructorTypeContext *> FormulogParser::AdtDefContext::constructorType() {
  return getRuleContexts<FormulogParser::ConstructorTypeContext>();
}

FormulogParser::ConstructorTypeContext* FormulogParser::AdtDefContext::constructorType(size_t i) {
  return getRuleContext<FormulogParser::ConstructorTypeContext>(i);
}


size_t FormulogParser::AdtDefContext::getRuleIndex() const {
  return FormulogParser::RuleAdtDef;
}

antlrcpp::Any FormulogParser::AdtDefContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitAdtDef(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::AdtDefContext* FormulogParser::adtDef() {
  AdtDefContext *_localctx = _tracker.createInstance<AdtDefContext>(_ctx, getState());
  enterRule(_localctx, 30, FormulogParser::RuleAdtDef);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(298);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 32, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(287);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__13) {
        setState(286);
        match(FormulogParser::T__13);
      }
      setState(289);
      constructorType();
      setState(294);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__13) {
        setState(290);
        match(FormulogParser::T__13);
        setState(291);
        constructorType();
        setState(296);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);

      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- RecordDefContext ------------------------------------------------------------------

FormulogParser::RecordDefContext::RecordDefContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::RecordEntryDefContext *> FormulogParser::RecordDefContext::recordEntryDef() {
  return getRuleContexts<FormulogParser::RecordEntryDefContext>();
}

FormulogParser::RecordEntryDefContext* FormulogParser::RecordDefContext::recordEntryDef(size_t i) {
  return getRuleContext<FormulogParser::RecordEntryDefContext>(i);
}


size_t FormulogParser::RecordDefContext::getRuleIndex() const {
  return FormulogParser::RuleRecordDef;
}

antlrcpp::Any FormulogParser::RecordDefContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRecordDef(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::RecordDefContext* FormulogParser::recordDef() {
  RecordDefContext *_localctx = _tracker.createInstance<RecordDefContext>(_ctx, getState());
  enterRule(_localctx, 32, FormulogParser::RuleRecordDef);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(300);
    match(FormulogParser::T__14);
    setState(301);
    recordEntryDef();
    setState(306);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 33, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(302);
        match(FormulogParser::T__15);
        setState(303);
        recordEntryDef(); 
      }
      setState(308);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 33, _ctx);
    }
    setState(310);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == FormulogParser::T__15) {
      setState(309);
      match(FormulogParser::T__15);
    }
    setState(312);
    match(FormulogParser::T__16);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- RecordEntryDefContext ------------------------------------------------------------------

FormulogParser::RecordEntryDefContext::RecordEntryDefContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::RecordEntryDefContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::TypeContext* FormulogParser::RecordEntryDefContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}


size_t FormulogParser::RecordEntryDefContext::getRuleIndex() const {
  return FormulogParser::RuleRecordEntryDef;
}

antlrcpp::Any FormulogParser::RecordEntryDefContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRecordEntryDef(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::RecordEntryDefContext* FormulogParser::recordEntryDef() {
  RecordEntryDefContext *_localctx = _tracker.createInstance<RecordEntryDefContext>(_ctx, getState());
  enterRule(_localctx, 34, FormulogParser::RuleRecordEntryDef);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(314);
    match(FormulogParser::ID);
    setState(315);
    match(FormulogParser::T__5);
    setState(316);
    type();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- AnnotationContext ------------------------------------------------------------------

FormulogParser::AnnotationContext::AnnotationContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::AnnotationContext::ID() {
  return getToken(FormulogParser::ID, 0);
}


size_t FormulogParser::AnnotationContext::getRuleIndex() const {
  return FormulogParser::RuleAnnotation;
}

antlrcpp::Any FormulogParser::AnnotationContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitAnnotation(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::AnnotationContext* FormulogParser::annotation() {
  AnnotationContext *_localctx = _tracker.createInstance<AnnotationContext>(_ctx, getState());
  enterRule(_localctx, 36, FormulogParser::RuleAnnotation);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(318);
    match(FormulogParser::T__17);
    setState(319);
    match(FormulogParser::ID);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- StmtContext ------------------------------------------------------------------

FormulogParser::StmtContext::StmtContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::StmtContext::getRuleIndex() const {
  return FormulogParser::RuleStmt;
}

void FormulogParser::StmtContext::copyFrom(StmtContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- ClauseStmtContext ------------------------------------------------------------------

FormulogParser::ClauseContext* FormulogParser::ClauseStmtContext::clause() {
  return getRuleContext<FormulogParser::ClauseContext>(0);
}

FormulogParser::ClauseStmtContext::ClauseStmtContext(StmtContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::ClauseStmtContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitClauseStmt(this);
  else
    return visitor->visitChildren(this);
}
//----------------- FactStmtContext ------------------------------------------------------------------

FormulogParser::FactContext* FormulogParser::FactStmtContext::fact() {
  return getRuleContext<FormulogParser::FactContext>(0);
}

FormulogParser::FactStmtContext::FactStmtContext(StmtContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::FactStmtContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFactStmt(this);
  else
    return visitor->visitChildren(this);
}
//----------------- QueryStmtContext ------------------------------------------------------------------

FormulogParser::QueryContext* FormulogParser::QueryStmtContext::query() {
  return getRuleContext<FormulogParser::QueryContext>(0);
}

FormulogParser::QueryStmtContext::QueryStmtContext(StmtContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::QueryStmtContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitQueryStmt(this);
  else
    return visitor->visitChildren(this);
}
FormulogParser::StmtContext* FormulogParser::stmt() {
  StmtContext *_localctx = _tracker.createInstance<StmtContext>(_ctx, getState());
  enterRule(_localctx, 38, FormulogParser::RuleStmt);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(324);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 35, _ctx)) {
    case 1: {
      _localctx = dynamic_cast<StmtContext *>(_tracker.createInstance<FormulogParser::ClauseStmtContext>(_localctx));
      enterOuterAlt(_localctx, 1);
      setState(321);
      clause();
      break;
    }

    case 2: {
      _localctx = dynamic_cast<StmtContext *>(_tracker.createInstance<FormulogParser::FactStmtContext>(_localctx));
      enterOuterAlt(_localctx, 2);
      setState(322);
      fact();
      break;
    }

    case 3: {
      _localctx = dynamic_cast<StmtContext *>(_tracker.createInstance<FormulogParser::QueryStmtContext>(_localctx));
      enterOuterAlt(_localctx, 3);
      setState(323);
      query();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ClauseContext ------------------------------------------------------------------

FormulogParser::ClauseContext::ClauseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::NonEmptyTermListContext *> FormulogParser::ClauseContext::nonEmptyTermList() {
  return getRuleContexts<FormulogParser::NonEmptyTermListContext>();
}

FormulogParser::NonEmptyTermListContext* FormulogParser::ClauseContext::nonEmptyTermList(size_t i) {
  return getRuleContext<FormulogParser::NonEmptyTermListContext>(i);
}


size_t FormulogParser::ClauseContext::getRuleIndex() const {
  return FormulogParser::RuleClause;
}

antlrcpp::Any FormulogParser::ClauseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitClause(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::ClauseContext* FormulogParser::clause() {
  ClauseContext *_localctx = _tracker.createInstance<ClauseContext>(_ctx, getState());
  enterRule(_localctx, 40, FormulogParser::RuleClause);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(326);
    dynamic_cast<ClauseContext *>(_localctx)->head = nonEmptyTermList();
    setState(327);
    match(FormulogParser::T__18);
    setState(328);
    dynamic_cast<ClauseContext *>(_localctx)->body = nonEmptyTermList();
    setState(329);
    match(FormulogParser::T__0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- FactContext ------------------------------------------------------------------

FormulogParser::FactContext::FactContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

FormulogParser::TermContext* FormulogParser::FactContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}


size_t FormulogParser::FactContext::getRuleIndex() const {
  return FormulogParser::RuleFact;
}

antlrcpp::Any FormulogParser::FactContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFact(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::FactContext* FormulogParser::fact() {
  FactContext *_localctx = _tracker.createInstance<FactContext>(_ctx, getState());
  enterRule(_localctx, 42, FormulogParser::RuleFact);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(331);
    term(0);
    setState(332);
    match(FormulogParser::T__0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- QueryContext ------------------------------------------------------------------

FormulogParser::QueryContext::QueryContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

FormulogParser::TermContext* FormulogParser::QueryContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}


size_t FormulogParser::QueryContext::getRuleIndex() const {
  return FormulogParser::RuleQuery;
}

antlrcpp::Any FormulogParser::QueryContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitQuery(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::QueryContext* FormulogParser::query() {
  QueryContext *_localctx = _tracker.createInstance<QueryContext>(_ctx, getState());
  enterRule(_localctx, 44, FormulogParser::RuleQuery);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(334);
    match(FormulogParser::T__18);
    setState(335);
    term(0);
    setState(336);
    match(FormulogParser::T__0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PredicateContext ------------------------------------------------------------------

FormulogParser::PredicateContext::PredicateContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::PredicateContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::TermArgsContext* FormulogParser::PredicateContext::termArgs() {
  return getRuleContext<FormulogParser::TermArgsContext>(0);
}


size_t FormulogParser::PredicateContext::getRuleIndex() const {
  return FormulogParser::RulePredicate;
}

antlrcpp::Any FormulogParser::PredicateContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitPredicate(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::PredicateContext* FormulogParser::predicate() {
  PredicateContext *_localctx = _tracker.createInstance<PredicateContext>(_ctx, getState());
  enterRule(_localctx, 46, FormulogParser::RulePredicate);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(338);
    match(FormulogParser::ID);
    setState(339);
    termArgs();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- FunctorContext ------------------------------------------------------------------

FormulogParser::FunctorContext::FunctorContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::FunctorContext::getRuleIndex() const {
  return FormulogParser::RuleFunctor;
}

void FormulogParser::FunctorContext::copyFrom(FunctorContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- IndexedFunctorContext ------------------------------------------------------------------

FormulogParser::ParameterListContext* FormulogParser::IndexedFunctorContext::parameterList() {
  return getRuleContext<FormulogParser::ParameterListContext>(0);
}

FormulogParser::TermArgsContext* FormulogParser::IndexedFunctorContext::termArgs() {
  return getRuleContext<FormulogParser::TermArgsContext>(0);
}

tree::TerminalNode* FormulogParser::IndexedFunctorContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

tree::TerminalNode* FormulogParser::IndexedFunctorContext::XID() {
  return getToken(FormulogParser::XID, 0);
}

tree::TerminalNode* FormulogParser::IndexedFunctorContext::XVAR() {
  return getToken(FormulogParser::XVAR, 0);
}

FormulogParser::IndexedFunctorContext::IndexedFunctorContext(FunctorContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::IndexedFunctorContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitIndexedFunctor(this);
  else
    return visitor->visitChildren(this);
}
FormulogParser::FunctorContext* FormulogParser::functor() {
  FunctorContext *_localctx = _tracker.createInstance<FunctorContext>(_ctx, getState());
  enterRule(_localctx, 48, FormulogParser::RuleFunctor);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    _localctx = dynamic_cast<FunctorContext *>(_tracker.createInstance<FormulogParser::IndexedFunctorContext>(_localctx));
    enterOuterAlt(_localctx, 1);
    setState(341);
    dynamic_cast<IndexedFunctorContext *>(_localctx)->id = _input->LT(1);
    _la = _input->LA(1);
    if (!(((((_la - 50) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 50)) & ((1ULL << (FormulogParser::XVAR - 50))
      | (1ULL << (FormulogParser::XID - 50))
      | (1ULL << (FormulogParser::ID - 50)))) != 0))) {
      dynamic_cast<IndexedFunctorContext *>(_localctx)->id = _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
    setState(342);
    parameterList();
    setState(343);
    termArgs();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TermArgsContext ------------------------------------------------------------------

FormulogParser::TermArgsContext::TermArgsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TermContext *> FormulogParser::TermArgsContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::TermArgsContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::TermArgsContext::getRuleIndex() const {
  return FormulogParser::RuleTermArgs;
}

antlrcpp::Any FormulogParser::TermArgsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTermArgs(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TermArgsContext* FormulogParser::termArgs() {
  TermArgsContext *_localctx = _tracker.createInstance<TermArgsContext>(_ctx, getState());
  enterRule(_localctx, 50, FormulogParser::RuleTermArgs);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(356);
    _errHandler->sync(this);

    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 37, _ctx)) {
    case 1: {
      setState(345);
      match(FormulogParser::T__7);

      setState(346);
      term(0);
      setState(351);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__8) {
        setState(347);
        match(FormulogParser::T__8);
        setState(348);
        term(0);
        setState(353);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(354);
      match(FormulogParser::T__9);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TermContext ------------------------------------------------------------------

FormulogParser::TermContext::TermContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}


size_t FormulogParser::TermContext::getRuleIndex() const {
  return FormulogParser::RuleTerm;
}

void FormulogParser::TermContext::copyFrom(TermContext *ctx) {
  ParserRuleContext::copyFrom(ctx);
}

//----------------- QuantifiedFormulaContext ------------------------------------------------------------------

std::vector<FormulogParser::NonEmptyTermListContext *> FormulogParser::QuantifiedFormulaContext::nonEmptyTermList() {
  return getRuleContexts<FormulogParser::NonEmptyTermListContext>();
}

FormulogParser::NonEmptyTermListContext* FormulogParser::QuantifiedFormulaContext::nonEmptyTermList(size_t i) {
  return getRuleContext<FormulogParser::NonEmptyTermListContext>(i);
}

FormulogParser::TermContext* FormulogParser::QuantifiedFormulaContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

tree::TerminalNode* FormulogParser::QuantifiedFormulaContext::FORALL() {
  return getToken(FormulogParser::FORALL, 0);
}

tree::TerminalNode* FormulogParser::QuantifiedFormulaContext::EXISTS() {
  return getToken(FormulogParser::EXISTS, 0);
}

FormulogParser::QuantifiedFormulaContext::QuantifiedFormulaContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::QuantifiedFormulaContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitQuantifiedFormula(this);
  else
    return visitor->visitChildren(this);
}
//----------------- BinopTermContext ------------------------------------------------------------------

std::vector<FormulogParser::TermContext *> FormulogParser::BinopTermContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::BinopTermContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

tree::TerminalNode* FormulogParser::BinopTermContext::MUL() {
  return getToken(FormulogParser::MUL, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::DIV() {
  return getToken(FormulogParser::DIV, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::REM() {
  return getToken(FormulogParser::REM, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::PLUS() {
  return getToken(FormulogParser::PLUS, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::MINUS() {
  return getToken(FormulogParser::MINUS, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::LT() {
  return getToken(FormulogParser::LT, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::LTE() {
  return getToken(FormulogParser::LTE, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::GT() {
  return getToken(FormulogParser::GT, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::GTE() {
  return getToken(FormulogParser::GTE, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::EQ() {
  return getToken(FormulogParser::EQ, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::NEQ() {
  return getToken(FormulogParser::NEQ, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::AMP() {
  return getToken(FormulogParser::AMP, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::CARET() {
  return getToken(FormulogParser::CARET, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::AMPAMP() {
  return getToken(FormulogParser::AMPAMP, 0);
}

tree::TerminalNode* FormulogParser::BinopTermContext::BARBAR() {
  return getToken(FormulogParser::BARBAR, 0);
}

FormulogParser::BinopTermContext::BinopTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::BinopTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitBinopTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- MatchExprContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::MatchExprContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

std::vector<FormulogParser::MatchClauseContext *> FormulogParser::MatchExprContext::matchClause() {
  return getRuleContexts<FormulogParser::MatchClauseContext>();
}

FormulogParser::MatchClauseContext* FormulogParser::MatchExprContext::matchClause(size_t i) {
  return getRuleContext<FormulogParser::MatchClauseContext>(i);
}

FormulogParser::MatchExprContext::MatchExprContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::MatchExprContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitMatchExpr(this);
  else
    return visitor->visitChildren(this);
}
//----------------- FunctorTermContext ------------------------------------------------------------------

FormulogParser::FunctorContext* FormulogParser::FunctorTermContext::functor() {
  return getRuleContext<FormulogParser::FunctorContext>(0);
}

FormulogParser::FunctorTermContext::FunctorTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::FunctorTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFunctorTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- I32TermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::I32TermContext::INT() {
  return getToken(FormulogParser::INT, 0);
}

tree::TerminalNode* FormulogParser::I32TermContext::HEX() {
  return getToken(FormulogParser::HEX, 0);
}

FormulogParser::I32TermContext::I32TermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::I32TermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitI32Term(this);
  else
    return visitor->visitChildren(this);
}
//----------------- NotFormulaContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::NotFormulaContext::NOT() {
  return getToken(FormulogParser::NOT, 0);
}

FormulogParser::TermContext* FormulogParser::NotFormulaContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

FormulogParser::NotFormulaContext::NotFormulaContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::NotFormulaContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitNotFormula(this);
  else
    return visitor->visitChildren(this);
}
//----------------- LetExprContext ------------------------------------------------------------------

FormulogParser::LetBindContext* FormulogParser::LetExprContext::letBind() {
  return getRuleContext<FormulogParser::LetBindContext>(0);
}

std::vector<FormulogParser::TermContext *> FormulogParser::LetExprContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::LetExprContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

FormulogParser::LetExprContext::LetExprContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::LetExprContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitLetExpr(this);
  else
    return visitor->visitChildren(this);
}
//----------------- FloatTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::FloatTermContext::FP32() {
  return getToken(FormulogParser::FP32, 0);
}

FormulogParser::FloatTermContext::FloatTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::FloatTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFloatTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- RecordTermContext ------------------------------------------------------------------

FormulogParser::RecordEntriesContext* FormulogParser::RecordTermContext::recordEntries() {
  return getRuleContext<FormulogParser::RecordEntriesContext>(0);
}

FormulogParser::RecordTermContext::RecordTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::RecordTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRecordTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- LetFormulaContext ------------------------------------------------------------------

std::vector<FormulogParser::TermContext *> FormulogParser::LetFormulaContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::LetFormulaContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

tree::TerminalNode* FormulogParser::LetFormulaContext::EQ() {
  return getToken(FormulogParser::EQ, 0);
}

FormulogParser::LetFormulaContext::LetFormulaContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::LetFormulaContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitLetFormula(this);
  else
    return visitor->visitChildren(this);
}
//----------------- UnopTermContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::UnopTermContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

tree::TerminalNode* FormulogParser::UnopTermContext::MINUS() {
  return getToken(FormulogParser::MINUS, 0);
}

tree::TerminalNode* FormulogParser::UnopTermContext::BANG() {
  return getToken(FormulogParser::BANG, 0);
}

FormulogParser::UnopTermContext::UnopTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::UnopTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitUnopTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- IfExprContext ------------------------------------------------------------------

std::vector<FormulogParser::TermContext *> FormulogParser::IfExprContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::IfExprContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

FormulogParser::IfExprContext::IfExprContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::IfExprContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitIfExpr(this);
  else
    return visitor->visitChildren(this);
}
//----------------- HoleTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::HoleTermContext::HOLE() {
  return getToken(FormulogParser::HOLE, 0);
}

FormulogParser::HoleTermContext::HoleTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::HoleTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitHoleTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- ListTermContext ------------------------------------------------------------------

FormulogParser::ListContext* FormulogParser::ListTermContext::list() {
  return getRuleContext<FormulogParser::ListContext>(0);
}

FormulogParser::ListTermContext::ListTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::ListTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitListTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- VarTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::VarTermContext::VAR() {
  return getToken(FormulogParser::VAR, 0);
}

FormulogParser::VarTermContext::VarTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::VarTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitVarTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- StringTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::StringTermContext::QSTRING() {
  return getToken(FormulogParser::QSTRING, 0);
}

FormulogParser::StringTermContext::StringTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::StringTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitStringTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- FormulaTermContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::FormulaTermContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

FormulogParser::FormulaTermContext::FormulaTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::FormulaTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFormulaTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- ConsTermContext ------------------------------------------------------------------

std::vector<FormulogParser::TermContext *> FormulogParser::ConsTermContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::ConsTermContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

FormulogParser::ConsTermContext::ConsTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::ConsTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitConsTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- TermSymFormulaContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::TermSymFormulaContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

FormulogParser::TypeContext* FormulogParser::TermSymFormulaContext::type() {
  return getRuleContext<FormulogParser::TypeContext>(0);
}

FormulogParser::TermSymFormulaContext::TermSymFormulaContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TermSymFormulaContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTermSymFormula(this);
  else
    return visitor->visitChildren(this);
}
//----------------- ParensTermContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::ParensTermContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

FormulogParser::ParensTermContext::ParensTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::ParensTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitParensTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- I64TermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::I64TermContext::I64() {
  return getToken(FormulogParser::I64, 0);
}

FormulogParser::I64TermContext::I64TermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::I64TermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitI64Term(this);
  else
    return visitor->visitChildren(this);
}
//----------------- IteTermContext ------------------------------------------------------------------

std::vector<FormulogParser::TermContext *> FormulogParser::IteTermContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::IteTermContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

FormulogParser::IteTermContext::IteTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::IteTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitIteTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- FoldTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::FoldTermContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::TermArgsContext* FormulogParser::FoldTermContext::termArgs() {
  return getRuleContext<FormulogParser::TermArgsContext>(0);
}

FormulogParser::FoldTermContext::FoldTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::FoldTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitFoldTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- SpecialFPTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::SpecialFPTermContext::FP32_NAN() {
  return getToken(FormulogParser::FP32_NAN, 0);
}

tree::TerminalNode* FormulogParser::SpecialFPTermContext::FP32_POS_INFINITY() {
  return getToken(FormulogParser::FP32_POS_INFINITY, 0);
}

tree::TerminalNode* FormulogParser::SpecialFPTermContext::FP32_NEG_INFINITY() {
  return getToken(FormulogParser::FP32_NEG_INFINITY, 0);
}

tree::TerminalNode* FormulogParser::SpecialFPTermContext::FP64_NAN() {
  return getToken(FormulogParser::FP64_NAN, 0);
}

tree::TerminalNode* FormulogParser::SpecialFPTermContext::FP64_POS_INFINITY() {
  return getToken(FormulogParser::FP64_POS_INFINITY, 0);
}

tree::TerminalNode* FormulogParser::SpecialFPTermContext::FP64_NEG_INFINITY() {
  return getToken(FormulogParser::FP64_NEG_INFINITY, 0);
}

FormulogParser::SpecialFPTermContext::SpecialFPTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::SpecialFPTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitSpecialFPTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- DoubleTermContext ------------------------------------------------------------------

tree::TerminalNode* FormulogParser::DoubleTermContext::FP64() {
  return getToken(FormulogParser::FP64, 0);
}

FormulogParser::DoubleTermContext::DoubleTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::DoubleTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitDoubleTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- LetFunExprContext ------------------------------------------------------------------

FormulogParser::FunDefsContext* FormulogParser::LetFunExprContext::funDefs() {
  return getRuleContext<FormulogParser::FunDefsContext>(0);
}

FormulogParser::TermContext* FormulogParser::LetFunExprContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

FormulogParser::LetFunExprContext::LetFunExprContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::LetFunExprContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitLetFunExpr(this);
  else
    return visitor->visitChildren(this);
}
//----------------- BinopFormulaContext ------------------------------------------------------------------

std::vector<FormulogParser::TermContext *> FormulogParser::BinopFormulaContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::BinopFormulaContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}

tree::TerminalNode* FormulogParser::BinopFormulaContext::FORMULA_EQ() {
  return getToken(FormulogParser::FORMULA_EQ, 0);
}

tree::TerminalNode* FormulogParser::BinopFormulaContext::AND() {
  return getToken(FormulogParser::AND, 0);
}

tree::TerminalNode* FormulogParser::BinopFormulaContext::OR() {
  return getToken(FormulogParser::OR, 0);
}

tree::TerminalNode* FormulogParser::BinopFormulaContext::IMP() {
  return getToken(FormulogParser::IMP, 0);
}

tree::TerminalNode* FormulogParser::BinopFormulaContext::IFF() {
  return getToken(FormulogParser::IFF, 0);
}

FormulogParser::BinopFormulaContext::BinopFormulaContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::BinopFormulaContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitBinopFormula(this);
  else
    return visitor->visitChildren(this);
}
//----------------- OutermostCtorContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::OutermostCtorContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

tree::TerminalNode* FormulogParser::OutermostCtorContext::ISNOT() {
  return getToken(FormulogParser::ISNOT, 0);
}

tree::TerminalNode* FormulogParser::OutermostCtorContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::OutermostCtorContext::OutermostCtorContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::OutermostCtorContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitOutermostCtor(this);
  else
    return visitor->visitChildren(this);
}
//----------------- TupleTermContext ------------------------------------------------------------------

FormulogParser::TupleContext* FormulogParser::TupleTermContext::tuple() {
  return getRuleContext<FormulogParser::TupleContext>(0);
}

FormulogParser::TupleTermContext::TupleTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::TupleTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTupleTerm(this);
  else
    return visitor->visitChildren(this);
}
//----------------- RecordUpdateTermContext ------------------------------------------------------------------

FormulogParser::TermContext* FormulogParser::RecordUpdateTermContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}

FormulogParser::RecordEntriesContext* FormulogParser::RecordUpdateTermContext::recordEntries() {
  return getRuleContext<FormulogParser::RecordEntriesContext>(0);
}

FormulogParser::RecordUpdateTermContext::RecordUpdateTermContext(TermContext *ctx) { copyFrom(ctx); }

antlrcpp::Any FormulogParser::RecordUpdateTermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRecordUpdateTerm(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TermContext* FormulogParser::term() {
   return term(0);
}

FormulogParser::TermContext* FormulogParser::term(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  FormulogParser::TermContext *_localctx = _tracker.createInstance<TermContext>(_ctx, parentState);
  FormulogParser::TermContext *previousContext = _localctx;
  size_t startState = 52;
  enterRecursionRule(_localctx, 52, FormulogParser::RuleTerm, precedence);

    size_t _la = 0;

  auto onExit = finally([=] {
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(463);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 41, _ctx)) {
    case 1: {
      _localctx = _tracker.createInstance<HoleTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;

      setState(359);
      match(FormulogParser::HOLE);
      break;
    }

    case 2: {
      _localctx = _tracker.createInstance<FoldTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(360);
      match(FormulogParser::T__19);
      setState(361);
      match(FormulogParser::T__10);
      setState(362);
      match(FormulogParser::ID);
      setState(363);
      match(FormulogParser::T__11);
      setState(364);
      termArgs();
      break;
    }

    case 3: {
      _localctx = _tracker.createInstance<FunctorTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(365);
      functor();
      break;
    }

    case 4: {
      _localctx = _tracker.createInstance<ListTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(366);
      list();
      break;
    }

    case 5: {
      _localctx = _tracker.createInstance<TupleTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(367);
      tuple();
      break;
    }

    case 6: {
      _localctx = _tracker.createInstance<ParensTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(368);
      match(FormulogParser::T__7);
      setState(369);
      term(0);
      setState(370);
      match(FormulogParser::T__9);
      break;
    }

    case 7: {
      _localctx = _tracker.createInstance<UnopTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(372);
      dynamic_cast<UnopTermContext *>(_localctx)->op = _input->LT(1);
      _la = _input->LA(1);
      if (!(_la == FormulogParser::MINUS

      || _la == FormulogParser::BANG)) {
        dynamic_cast<UnopTermContext *>(_localctx)->op = _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(373);
      term(35);
      break;
    }

    case 8: {
      _localctx = _tracker.createInstance<VarTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(374);
      match(FormulogParser::VAR);
      break;
    }

    case 9: {
      _localctx = _tracker.createInstance<StringTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(375);
      match(FormulogParser::QSTRING);
      break;
    }

    case 10: {
      _localctx = _tracker.createInstance<I32TermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(376);
      dynamic_cast<I32TermContext *>(_localctx)->val = _input->LT(1);
      _la = _input->LA(1);
      if (!(_la == FormulogParser::INT

      || _la == FormulogParser::HEX)) {
        dynamic_cast<I32TermContext *>(_localctx)->val = _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      break;
    }

    case 11: {
      _localctx = _tracker.createInstance<I64TermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(377);
      dynamic_cast<I64TermContext *>(_localctx)->val = match(FormulogParser::I64);
      break;
    }

    case 12: {
      _localctx = _tracker.createInstance<DoubleTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(378);
      dynamic_cast<DoubleTermContext *>(_localctx)->val = match(FormulogParser::FP64);
      break;
    }

    case 13: {
      _localctx = _tracker.createInstance<FloatTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(379);
      dynamic_cast<FloatTermContext *>(_localctx)->val = match(FormulogParser::FP32);
      break;
    }

    case 14: {
      _localctx = _tracker.createInstance<SpecialFPTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(380);
      dynamic_cast<SpecialFPTermContext *>(_localctx)->val = _input->LT(1);
      _la = _input->LA(1);
      if (!((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << FormulogParser::FP32_NAN)
        | (1ULL << FormulogParser::FP32_POS_INFINITY)
        | (1ULL << FormulogParser::FP32_NEG_INFINITY)
        | (1ULL << FormulogParser::FP64_NAN)
        | (1ULL << FormulogParser::FP64_POS_INFINITY)
        | (1ULL << FormulogParser::FP64_NEG_INFINITY))) != 0))) {
        dynamic_cast<SpecialFPTermContext *>(_localctx)->val = _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      break;
    }

    case 15: {
      _localctx = _tracker.createInstance<RecordTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(381);
      match(FormulogParser::T__14);
      setState(382);
      recordEntries();
      setState(383);
      match(FormulogParser::T__16);
      break;
    }

    case 16: {
      _localctx = _tracker.createInstance<RecordUpdateTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(385);
      match(FormulogParser::T__14);
      setState(386);
      term(0);
      setState(387);
      match(FormulogParser::T__21);
      setState(388);
      recordEntries();
      setState(389);
      match(FormulogParser::T__16);
      break;
    }

    case 17: {
      _localctx = _tracker.createInstance<FormulaTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(391);
      match(FormulogParser::T__22);
      setState(392);
      term(0);
      setState(393);
      match(FormulogParser::T__22);
      break;
    }

    case 18: {
      _localctx = _tracker.createInstance<TermSymFormulaContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(395);
      match(FormulogParser::T__23);
      setState(396);
      match(FormulogParser::T__14);
      setState(397);
      term(0);
      setState(398);
      match(FormulogParser::T__16);
      setState(399);
      match(FormulogParser::T__10);
      setState(400);
      type();
      setState(401);
      match(FormulogParser::T__11);
      break;
    }

    case 19: {
      _localctx = _tracker.createInstance<NotFormulaContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(403);
      match(FormulogParser::NOT);
      setState(404);
      term(14);
      break;
    }

    case 20: {
      _localctx = _tracker.createInstance<LetFormulaContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(405);
      match(FormulogParser::T__24);
      setState(406);
      term(0);
      setState(407);
      match(FormulogParser::EQ);
      setState(408);
      term(0);
      setState(409);
      match(FormulogParser::T__25);
      setState(410);
      term(8);
      break;
    }

    case 21: {
      _localctx = _tracker.createInstance<QuantifiedFormulaContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(412);
      dynamic_cast<QuantifiedFormulaContext *>(_localctx)->quantifier = _input->LT(1);
      _la = _input->LA(1);
      if (!(_la == FormulogParser::FORALL

      || _la == FormulogParser::EXISTS)) {
        dynamic_cast<QuantifiedFormulaContext *>(_localctx)->quantifier = _errHandler->recoverInline(this);
      }
      else {
        _errHandler->reportMatch(this);
        consume();
      }
      setState(413);
      dynamic_cast<QuantifiedFormulaContext *>(_localctx)->variables = nonEmptyTermList();
      setState(416);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__5) {
        setState(414);
        match(FormulogParser::T__5);
        setState(415);
        dynamic_cast<QuantifiedFormulaContext *>(_localctx)->pattern = nonEmptyTermList();
      }
      setState(418);
      match(FormulogParser::T__0);
      setState(419);
      dynamic_cast<QuantifiedFormulaContext *>(_localctx)->boundTerm = term(7);
      break;
    }

    case 22: {
      _localctx = _tracker.createInstance<IteTermContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(421);
      match(FormulogParser::T__26);
      setState(422);
      term(0);
      setState(423);
      match(FormulogParser::T__27);
      setState(424);
      term(0);
      setState(425);
      match(FormulogParser::T__28);
      setState(426);
      term(6);
      break;
    }

    case 23: {
      _localctx = _tracker.createInstance<MatchExprContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(428);
      match(FormulogParser::T__29);
      setState(429);
      term(0);
      setState(430);
      match(FormulogParser::T__21);
      setState(432);
      _errHandler->sync(this);

      _la = _input->LA(1);
      if (_la == FormulogParser::T__13) {
        setState(431);
        match(FormulogParser::T__13);
      }
      setState(434);
      matchClause();
      setState(439);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__13) {
        setState(435);
        match(FormulogParser::T__13);
        setState(436);
        matchClause();
        setState(441);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(442);
      match(FormulogParser::T__30);
      break;
    }

    case 24: {
      _localctx = _tracker.createInstance<LetExprContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(444);
      match(FormulogParser::T__31);
      setState(445);
      dynamic_cast<LetExprContext *>(_localctx)->lhs = letBind();
      setState(446);
      match(FormulogParser::EQ);
      setState(447);
      dynamic_cast<LetExprContext *>(_localctx)->assign = term(0);
      setState(448);
      match(FormulogParser::T__25);
      setState(449);
      dynamic_cast<LetExprContext *>(_localctx)->body = term(3);
      break;
    }

    case 25: {
      _localctx = _tracker.createInstance<LetFunExprContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(451);
      match(FormulogParser::T__31);
      setState(452);
      funDefs();
      setState(453);
      match(FormulogParser::T__25);
      setState(454);
      dynamic_cast<LetFunExprContext *>(_localctx)->letFunBody = term(2);
      break;
    }

    case 26: {
      _localctx = _tracker.createInstance<IfExprContext>(_localctx);
      _ctx = _localctx;
      previousContext = _localctx;
      setState(456);
      match(FormulogParser::T__32);
      setState(457);
      dynamic_cast<IfExprContext *>(_localctx)->guard = term(0);
      setState(458);
      match(FormulogParser::T__27);
      setState(459);
      dynamic_cast<IfExprContext *>(_localctx)->thenExpr = term(0);
      setState(460);
      match(FormulogParser::T__28);
      setState(461);
      dynamic_cast<IfExprContext *>(_localctx)->elseExpr = term(1);
      break;
    }

    }
    _ctx->stop = _input->LT(-1);
    setState(512);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 43, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(510);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 42, _ctx)) {
        case 1: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(465);

          if (!(precpred(_ctx, 34))) throw FailedPredicateException(this, "precpred(_ctx, 34)");
          setState(466);
          dynamic_cast<BinopTermContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!((((_la & ~ 0x3fULL) == 0) &&
            ((1ULL << _la) & ((1ULL << FormulogParser::MUL)
            | (1ULL << FormulogParser::DIV)
            | (1ULL << FormulogParser::REM))) != 0))) {
            dynamic_cast<BinopTermContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(467);
          term(35);
          break;
        }

        case 2: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(468);

          if (!(precpred(_ctx, 33))) throw FailedPredicateException(this, "precpred(_ctx, 33)");
          setState(469);
          dynamic_cast<BinopTermContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!(_la == FormulogParser::PLUS

          || _la == FormulogParser::MINUS)) {
            dynamic_cast<BinopTermContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(470);
          term(34);
          break;
        }

        case 3: {
          auto newContext = _tracker.createInstance<ConsTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(471);

          if (!(precpred(_ctx, 32))) throw FailedPredicateException(this, "precpred(_ctx, 32)");
          setState(472);
          match(FormulogParser::T__20);
          setState(473);
          term(32);
          break;
        }

        case 4: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(474);

          if (!(precpred(_ctx, 31))) throw FailedPredicateException(this, "precpred(_ctx, 31)");
          setState(475);
          dynamic_cast<BinopTermContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!((((_la & ~ 0x3fULL) == 0) &&
            ((1ULL << _la) & ((1ULL << FormulogParser::LT)
            | (1ULL << FormulogParser::LTE)
            | (1ULL << FormulogParser::GT)
            | (1ULL << FormulogParser::GTE))) != 0))) {
            dynamic_cast<BinopTermContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(476);
          term(32);
          break;
        }

        case 5: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(477);

          if (!(precpred(_ctx, 30))) throw FailedPredicateException(this, "precpred(_ctx, 30)");
          setState(478);
          dynamic_cast<BinopTermContext *>(_localctx)->op = _input->LT(1);
          _la = _input->LA(1);
          if (!(_la == FormulogParser::EQ

          || _la == FormulogParser::NEQ)) {
            dynamic_cast<BinopTermContext *>(_localctx)->op = _errHandler->recoverInline(this);
          }
          else {
            _errHandler->reportMatch(this);
            consume();
          }
          setState(479);
          term(31);
          break;
        }

        case 6: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(480);

          if (!(precpred(_ctx, 29))) throw FailedPredicateException(this, "precpred(_ctx, 29)");
          setState(481);
          dynamic_cast<BinopTermContext *>(_localctx)->op = match(FormulogParser::AMP);
          setState(482);
          term(30);
          break;
        }

        case 7: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(483);

          if (!(precpred(_ctx, 28))) throw FailedPredicateException(this, "precpred(_ctx, 28)");
          setState(484);
          dynamic_cast<BinopTermContext *>(_localctx)->op = match(FormulogParser::CARET);
          setState(485);
          term(29);
          break;
        }

        case 8: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(486);

          if (!(precpred(_ctx, 27))) throw FailedPredicateException(this, "precpred(_ctx, 27)");
          setState(487);
          dynamic_cast<BinopTermContext *>(_localctx)->op = match(FormulogParser::AMPAMP);
          setState(488);
          term(28);
          break;
        }

        case 9: {
          auto newContext = _tracker.createInstance<BinopTermContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(489);

          if (!(precpred(_ctx, 26))) throw FailedPredicateException(this, "precpred(_ctx, 26)");
          setState(490);
          dynamic_cast<BinopTermContext *>(_localctx)->op = match(FormulogParser::BARBAR);
          setState(491);
          term(27);
          break;
        }

        case 10: {
          auto newContext = _tracker.createInstance<BinopFormulaContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(492);

          if (!(precpred(_ctx, 13))) throw FailedPredicateException(this, "precpred(_ctx, 13)");
          setState(493);
          dynamic_cast<BinopFormulaContext *>(_localctx)->op = match(FormulogParser::FORMULA_EQ);
          setState(494);
          term(14);
          break;
        }

        case 11: {
          auto newContext = _tracker.createInstance<BinopFormulaContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(495);

          if (!(precpred(_ctx, 12))) throw FailedPredicateException(this, "precpred(_ctx, 12)");
          setState(496);
          dynamic_cast<BinopFormulaContext *>(_localctx)->op = match(FormulogParser::AND);
          setState(497);
          term(12);
          break;
        }

        case 12: {
          auto newContext = _tracker.createInstance<BinopFormulaContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(498);

          if (!(precpred(_ctx, 11))) throw FailedPredicateException(this, "precpred(_ctx, 11)");
          setState(499);
          dynamic_cast<BinopFormulaContext *>(_localctx)->op = match(FormulogParser::OR);
          setState(500);
          term(11);
          break;
        }

        case 13: {
          auto newContext = _tracker.createInstance<BinopFormulaContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(501);

          if (!(precpred(_ctx, 10))) throw FailedPredicateException(this, "precpred(_ctx, 10)");
          setState(502);
          dynamic_cast<BinopFormulaContext *>(_localctx)->op = match(FormulogParser::IMP);
          setState(503);
          term(10);
          break;
        }

        case 14: {
          auto newContext = _tracker.createInstance<BinopFormulaContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(504);

          if (!(precpred(_ctx, 9))) throw FailedPredicateException(this, "precpred(_ctx, 9)");
          setState(505);
          dynamic_cast<BinopFormulaContext *>(_localctx)->op = match(FormulogParser::IFF);
          setState(506);
          term(9);
          break;
        }

        case 15: {
          auto newContext = _tracker.createInstance<OutermostCtorContext>(_tracker.createInstance<TermContext>(parentContext, parentState));
          _localctx = newContext;
          pushNewRecursionContext(newContext, startState, RuleTerm);
          setState(507);

          if (!(precpred(_ctx, 5))) throw FailedPredicateException(this, "precpred(_ctx, 5)");
          setState(508);
          match(FormulogParser::ISNOT);
          setState(509);
          match(FormulogParser::ID);
          break;
        }

        } 
      }
      setState(514);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 43, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- RecordEntriesContext ------------------------------------------------------------------

FormulogParser::RecordEntriesContext::RecordEntriesContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::RecordEntryContext *> FormulogParser::RecordEntriesContext::recordEntry() {
  return getRuleContexts<FormulogParser::RecordEntryContext>();
}

FormulogParser::RecordEntryContext* FormulogParser::RecordEntriesContext::recordEntry(size_t i) {
  return getRuleContext<FormulogParser::RecordEntryContext>(i);
}


size_t FormulogParser::RecordEntriesContext::getRuleIndex() const {
  return FormulogParser::RuleRecordEntries;
}

antlrcpp::Any FormulogParser::RecordEntriesContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRecordEntries(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::RecordEntriesContext* FormulogParser::recordEntries() {
  RecordEntriesContext *_localctx = _tracker.createInstance<RecordEntriesContext>(_ctx, getState());
  enterRule(_localctx, 54, FormulogParser::RuleRecordEntries);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(515);
    recordEntry();
    setState(520);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 44, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        setState(516);
        match(FormulogParser::T__15);
        setState(517);
        recordEntry(); 
      }
      setState(522);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 44, _ctx);
    }
    setState(524);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == FormulogParser::T__15) {
      setState(523);
      match(FormulogParser::T__15);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- RecordEntryContext ------------------------------------------------------------------

FormulogParser::RecordEntryContext::RecordEntryContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* FormulogParser::RecordEntryContext::ID() {
  return getToken(FormulogParser::ID, 0);
}

FormulogParser::TermContext* FormulogParser::RecordEntryContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}


size_t FormulogParser::RecordEntryContext::getRuleIndex() const {
  return FormulogParser::RuleRecordEntry;
}

antlrcpp::Any FormulogParser::RecordEntryContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitRecordEntry(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::RecordEntryContext* FormulogParser::recordEntry() {
  RecordEntryContext *_localctx = _tracker.createInstance<RecordEntryContext>(_ctx, getState());
  enterRule(_localctx, 56, FormulogParser::RuleRecordEntry);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(526);
    match(FormulogParser::ID);
    setState(527);
    match(FormulogParser::EQ);
    setState(528);
    term(0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- LetBindContext ------------------------------------------------------------------

FormulogParser::LetBindContext::LetBindContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TermContext *> FormulogParser::LetBindContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::LetBindContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::LetBindContext::getRuleIndex() const {
  return FormulogParser::RuleLetBind;
}

antlrcpp::Any FormulogParser::LetBindContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitLetBind(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::LetBindContext* FormulogParser::letBind() {
  LetBindContext *_localctx = _tracker.createInstance<LetBindContext>(_ctx, getState());
  enterRule(_localctx, 58, FormulogParser::RuleLetBind);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(544);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 47, _ctx)) {
    case 1: {
      setState(530);
      term(0);
      break;
    }

    case 2: {
      setState(531);
      match(FormulogParser::T__7);
      setState(532);
      term(0);
      setState(533);
      match(FormulogParser::T__8);
      setState(534);
      term(0);
      setState(539);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__8) {
        setState(535);
        match(FormulogParser::T__8);
        setState(536);
        term(0);
        setState(541);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(542);
      match(FormulogParser::T__9);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- NonEmptyTermListContext ------------------------------------------------------------------

FormulogParser::NonEmptyTermListContext::NonEmptyTermListContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TermContext *> FormulogParser::NonEmptyTermListContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::NonEmptyTermListContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::NonEmptyTermListContext::getRuleIndex() const {
  return FormulogParser::RuleNonEmptyTermList;
}

antlrcpp::Any FormulogParser::NonEmptyTermListContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitNonEmptyTermList(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::NonEmptyTermListContext* FormulogParser::nonEmptyTermList() {
  NonEmptyTermListContext *_localctx = _tracker.createInstance<NonEmptyTermListContext>(_ctx, getState());
  enterRule(_localctx, 60, FormulogParser::RuleNonEmptyTermList);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(546);
    term(0);
    setState(551);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == FormulogParser::T__8) {
      setState(547);
      match(FormulogParser::T__8);
      setState(548);
      term(0);
      setState(553);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ListContext ------------------------------------------------------------------

FormulogParser::ListContext::ListContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TermContext *> FormulogParser::ListContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::ListContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::ListContext::getRuleIndex() const {
  return FormulogParser::RuleList;
}

antlrcpp::Any FormulogParser::ListContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitList(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::ListContext* FormulogParser::list() {
  ListContext *_localctx = _tracker.createInstance<ListContext>(_ctx, getState());
  enterRule(_localctx, 62, FormulogParser::RuleList);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(554);
    match(FormulogParser::T__10);
    setState(563);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << FormulogParser::T__7)
      | (1ULL << FormulogParser::T__10)
      | (1ULL << FormulogParser::T__14)
      | (1ULL << FormulogParser::T__19)
      | (1ULL << FormulogParser::T__22)
      | (1ULL << FormulogParser::T__23)
      | (1ULL << FormulogParser::T__24)
      | (1ULL << FormulogParser::T__26)
      | (1ULL << FormulogParser::T__29)
      | (1ULL << FormulogParser::T__31)
      | (1ULL << FormulogParser::T__32)
      | (1ULL << FormulogParser::NOT)
      | (1ULL << FormulogParser::FP32_NAN)
      | (1ULL << FormulogParser::FP32_POS_INFINITY)
      | (1ULL << FormulogParser::FP32_NEG_INFINITY)
      | (1ULL << FormulogParser::FP64_NAN)
      | (1ULL << FormulogParser::FP64_POS_INFINITY)
      | (1ULL << FormulogParser::FP64_NEG_INFINITY)
      | (1ULL << FormulogParser::XVAR)
      | (1ULL << FormulogParser::VAR)
      | (1ULL << FormulogParser::INT)
      | (1ULL << FormulogParser::HEX)
      | (1ULL << FormulogParser::FP32)
      | (1ULL << FormulogParser::FP64)
      | (1ULL << FormulogParser::I64))) != 0) || ((((_la - 65) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 65)) & ((1ULL << (FormulogParser::MINUS - 65))
      | (1ULL << (FormulogParser::BANG - 65))
      | (1ULL << (FormulogParser::FORALL - 65))
      | (1ULL << (FormulogParser::EXISTS - 65))
      | (1ULL << (FormulogParser::HOLE - 65))
      | (1ULL << (FormulogParser::XID - 65))
      | (1ULL << (FormulogParser::ID - 65))
      | (1ULL << (FormulogParser::QSTRING - 65)))) != 0)) {
      setState(555);
      term(0);
      setState(560);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (_la == FormulogParser::T__8) {
        setState(556);
        match(FormulogParser::T__8);
        setState(557);
        term(0);
        setState(562);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
    }
    setState(565);
    match(FormulogParser::T__11);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TupleContext ------------------------------------------------------------------

FormulogParser::TupleContext::TupleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TermContext *> FormulogParser::TupleContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::TupleContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::TupleContext::getRuleIndex() const {
  return FormulogParser::RuleTuple;
}

antlrcpp::Any FormulogParser::TupleContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitTuple(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::TupleContext* FormulogParser::tuple() {
  TupleContext *_localctx = _tracker.createInstance<TupleContext>(_ctx, getState());
  enterRule(_localctx, 64, FormulogParser::RuleTuple);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(567);
    match(FormulogParser::T__7);
    setState(568);
    term(0);
    setState(569);
    match(FormulogParser::T__8);
    setState(570);
    term(0);
    setState(575);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == FormulogParser::T__8) {
      setState(571);
      match(FormulogParser::T__8);
      setState(572);
      term(0);
      setState(577);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(578);
    match(FormulogParser::T__9);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- MatchClauseContext ------------------------------------------------------------------

FormulogParser::MatchClauseContext::MatchClauseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

FormulogParser::PatternsContext* FormulogParser::MatchClauseContext::patterns() {
  return getRuleContext<FormulogParser::PatternsContext>(0);
}

FormulogParser::TermContext* FormulogParser::MatchClauseContext::term() {
  return getRuleContext<FormulogParser::TermContext>(0);
}


size_t FormulogParser::MatchClauseContext::getRuleIndex() const {
  return FormulogParser::RuleMatchClause;
}

antlrcpp::Any FormulogParser::MatchClauseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitMatchClause(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::MatchClauseContext* FormulogParser::matchClause() {
  MatchClauseContext *_localctx = _tracker.createInstance<MatchClauseContext>(_ctx, getState());
  enterRule(_localctx, 66, FormulogParser::RuleMatchClause);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(580);
    dynamic_cast<MatchClauseContext *>(_localctx)->pats = patterns();
    setState(581);
    match(FormulogParser::T__33);
    setState(582);
    dynamic_cast<MatchClauseContext *>(_localctx)->rhs = term(0);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PatternsContext ------------------------------------------------------------------

FormulogParser::PatternsContext::PatternsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<FormulogParser::TermContext *> FormulogParser::PatternsContext::term() {
  return getRuleContexts<FormulogParser::TermContext>();
}

FormulogParser::TermContext* FormulogParser::PatternsContext::term(size_t i) {
  return getRuleContext<FormulogParser::TermContext>(i);
}


size_t FormulogParser::PatternsContext::getRuleIndex() const {
  return FormulogParser::RulePatterns;
}

antlrcpp::Any FormulogParser::PatternsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<FormulogVisitor*>(visitor))
    return parserVisitor->visitPatterns(this);
  else
    return visitor->visitChildren(this);
}

FormulogParser::PatternsContext* FormulogParser::patterns() {
  PatternsContext *_localctx = _tracker.createInstance<PatternsContext>(_ctx, getState());
  enterRule(_localctx, 68, FormulogParser::RulePatterns);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(584);
    term(0);
    setState(589);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == FormulogParser::T__13) {
      setState(585);
      match(FormulogParser::T__13);
      setState(586);
      term(0);
      setState(591);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

bool FormulogParser::sempred(RuleContext *context, size_t ruleIndex, size_t predicateIndex) {
  switch (ruleIndex) {
    case 9: return type0Sempred(dynamic_cast<Type0Context *>(context), predicateIndex);
    case 26: return termSempred(dynamic_cast<TermContext *>(context), predicateIndex);

  default:
    break;
  }
  return true;
}

bool FormulogParser::type0Sempred(Type0Context *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 0: return precpred(_ctx, 2);

  default:
    break;
  }
  return true;
}

bool FormulogParser::termSempred(TermContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 1: return precpred(_ctx, 34);
    case 2: return precpred(_ctx, 33);
    case 3: return precpred(_ctx, 32);
    case 4: return precpred(_ctx, 31);
    case 5: return precpred(_ctx, 30);
    case 6: return precpred(_ctx, 29);
    case 7: return precpred(_ctx, 28);
    case 8: return precpred(_ctx, 27);
    case 9: return precpred(_ctx, 26);
    case 10: return precpred(_ctx, 13);
    case 11: return precpred(_ctx, 12);
    case 12: return precpred(_ctx, 11);
    case 13: return precpred(_ctx, 10);
    case 14: return precpred(_ctx, 9);
    case 15: return precpred(_ctx, 5);

  default:
    break;
  }
  return true;
}

// Static vars and initialization.
std::vector<dfa::DFA> FormulogParser::_decisionToDFA;
atn::PredictionContextCache FormulogParser::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN FormulogParser::_atn;
std::vector<uint16_t> FormulogParser::_serializedATN;

std::vector<std::string> FormulogParser::_ruleNames = {
  "prog", "tsvFile", "tabSeparatedTermLine", "metadata", "funDefLHS", "funDefs", 
  "constructorType", "varTypeList", "typeList", "type0", "type", "parameterList", 
  "parameter", "typeDefLHS", "typeDefRHS", "adtDef", "recordDef", "recordEntryDef", 
  "annotation", "stmt", "clause", "fact", "query", "predicate", "functor", 
  "termArgs", "term", "recordEntries", "recordEntry", "letBind", "nonEmptyTermList", 
  "list", "tuple", "matchClause", "patterns"
};

std::vector<std::string> FormulogParser::_literalNames = {
  "", "'.'", "'type'", "'and'", "'uninterpreted'", "'fun'", "':'", "'sort'", 
  "'('", "','", "')'", "'['", "']'", "'?'", "'|'", "'{'", "';'", "'}'", 
  "'@'", "':-'", "'fold'", "'::'", "'with'", "'`'", "'#'", "'#let'", "'in'", 
  "'#if'", "'then'", "'else'", "'match'", "'end'", "'let'", "'if'", "'=>'", 
  "'/\\'", "'\\/'", "'==>'", "'<==>'", "'~'", "'#='", "'input'", "'output'", 
  "'fp32_nan'", "'fp32_pos_infinity'", "'fp32_neg_infinity'", "'fp64_nan'", 
  "'fp64_pos_infinity'", "'fp64_neg_infinity'", "", "", "", "", "", "", 
  "", "", "'<'", "'<='", "'>'", "'>='", "'*'", "'/'", "'%'", "'+'", "'-'", 
  "'!'", "'^'", "'&'", "'||'", "'&&'", "'not'", "'='", "'!='", "'forall'", 
  "'exists'", "'??'", "", "'\t'"
};

std::vector<std::string> FormulogParser::_symbolicNames = {
  "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", 
  "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "AND", 
  "OR", "IMP", "IFF", "NOT", "FORMULA_EQ", "INPUT", "OUTPUT", "FP32_NAN", 
  "FP32_POS_INFINITY", "FP32_NEG_INFINITY", "FP64_NAN", "FP64_POS_INFINITY", 
  "FP64_NEG_INFINITY", "TYPEVAR", "XVAR", "VAR", "INT", "HEX", "FP32", "FP64", 
  "I64", "LT", "LTE", "GT", "GTE", "MUL", "DIV", "REM", "PLUS", "MINUS", 
  "BANG", "CARET", "AMP", "BARBAR", "AMPAMP", "ISNOT", "EQ", "NEQ", "FORALL", 
  "EXISTS", "HOLE", "NEWLINE", "TAB", "SPACES", "COMMENT", "XID", "ID", 
  "QSTRING"
};

dfa::Vocabulary FormulogParser::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> FormulogParser::_tokenNames;

FormulogParser::Initializer::Initializer() {
	for (size_t i = 0; i < _symbolicNames.size(); ++i) {
		std::string name = _vocabulary.getLiteralName(i);
		if (name.empty()) {
			name = _vocabulary.getSymbolicName(i);
		}

		if (name.empty()) {
			_tokenNames.push_back("<INVALID>");
		} else {
      _tokenNames.push_back(name);
    }
	}

  _serializedATN = {
    0x3, 0x608b, 0xa72a, 0x8133, 0xb9ed, 0x417c, 0x3be7, 0x7786, 0x5964, 
    0x3, 0x55, 0x253, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 0x4, 
    0x9, 0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 0x7, 
    0x4, 0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 0xb, 
    0x9, 0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 0xe, 
    0x4, 0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 0x4, 
    0x12, 0x9, 0x12, 0x4, 0x13, 0x9, 0x13, 0x4, 0x14, 0x9, 0x14, 0x4, 0x15, 
    0x9, 0x15, 0x4, 0x16, 0x9, 0x16, 0x4, 0x17, 0x9, 0x17, 0x4, 0x18, 0x9, 
    0x18, 0x4, 0x19, 0x9, 0x19, 0x4, 0x1a, 0x9, 0x1a, 0x4, 0x1b, 0x9, 0x1b, 
    0x4, 0x1c, 0x9, 0x1c, 0x4, 0x1d, 0x9, 0x1d, 0x4, 0x1e, 0x9, 0x1e, 0x4, 
    0x1f, 0x9, 0x1f, 0x4, 0x20, 0x9, 0x20, 0x4, 0x21, 0x9, 0x21, 0x4, 0x22, 
    0x9, 0x22, 0x4, 0x23, 0x9, 0x23, 0x4, 0x24, 0x9, 0x24, 0x3, 0x2, 0x3, 
    0x2, 0x7, 0x2, 0x4b, 0xa, 0x2, 0xc, 0x2, 0xe, 0x2, 0x4e, 0xb, 0x2, 0x3, 
    0x2, 0x3, 0x2, 0x3, 0x3, 0x7, 0x3, 0x53, 0xa, 0x3, 0xc, 0x3, 0xe, 0x3, 
    0x56, 0xb, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x4, 0x3, 0x4, 0x3, 0x4, 0x7, 
    0x4, 0x5d, 0xa, 0x4, 0xc, 0x4, 0xe, 0x4, 0x60, 0xb, 0x4, 0x5, 0x4, 0x62, 
    0xa, 0x4, 0x3, 0x4, 0x3, 0x4, 0x3, 0x5, 0x3, 0x5, 0x5, 0x5, 0x68, 0xa, 
    0x5, 0x3, 0x5, 0x7, 0x5, 0x6b, 0xa, 0x5, 0xc, 0x5, 0xe, 0x5, 0x6e, 0xb, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x5, 0x5, 0x74, 0xa, 0x5, 
    0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x5, 0x5, 0x7b, 0xa, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x7, 0x5, 0x86, 0xa, 0x5, 0xc, 0x5, 0xe, 0x5, 
    0x89, 0xb, 0x5, 0x3, 0x5, 0x5, 0x5, 0x8c, 0xa, 0x5, 0x3, 0x5, 0x3, 0x5, 
    0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x5, 0x5, 0x94, 0xa, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x5, 0x5, 0x9a, 0xa, 0x5, 0x5, 0x5, 
    0x9c, 0xa, 0x5, 0x3, 0x6, 0x3, 0x6, 0x3, 0x6, 0x3, 0x6, 0x3, 0x6, 0x3, 
    0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 
    0x7, 0x3, 0x7, 0x7, 0x7, 0xac, 0xa, 0x7, 0xc, 0x7, 0xe, 0x7, 0xaf, 0xb, 
    0x7, 0x3, 0x8, 0x3, 0x8, 0x3, 0x8, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 
    0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x7, 0x9, 0xbc, 0xa, 0x9, 
    0xc, 0x9, 0xe, 0x9, 0xbf, 0xb, 0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x5, 
    0x9, 0xc4, 0xa, 0x9, 0x3, 0xa, 0x3, 0xa, 0x3, 0xa, 0x3, 0xa, 0x7, 0xa, 
    0xca, 0xa, 0xa, 0xc, 0xa, 0xe, 0xa, 0xcd, 0xb, 0xa, 0x3, 0xa, 0x3, 0xa, 
    0x3, 0xa, 0x5, 0xa, 0xd2, 0xa, 0xa, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 
    0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x7, 
    0xb, 0xde, 0xa, 0xb, 0xc, 0xb, 0xe, 0xb, 0xe1, 0xb, 0xb, 0x3, 0xb, 0x3, 
    0xb, 0x5, 0xb, 0xe5, 0xa, 0xb, 0x3, 0xb, 0x3, 0xb, 0x5, 0xb, 0xe9, 0xa, 
    0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x7, 0xb, 0xee, 0xa, 0xb, 0xc, 0xb, 
    0xe, 0xb, 0xf1, 0xb, 0xb, 0x3, 0xc, 0x3, 0xc, 0x3, 0xc, 0x7, 0xc, 0xf6, 
    0xa, 0xc, 0xc, 0xc, 0xe, 0xc, 0xf9, 0xb, 0xc, 0x3, 0xd, 0x3, 0xd, 0x3, 
    0xd, 0x3, 0xd, 0x7, 0xd, 0xff, 0xa, 0xd, 0xc, 0xd, 0xe, 0xd, 0x102, 
    0xb, 0xd, 0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x5, 0xd, 0x107, 0xa, 0xd, 0x3, 
    0xe, 0x3, 0xe, 0x3, 0xe, 0x5, 0xe, 0x10c, 0xa, 0xe, 0x3, 0xf, 0x3, 0xf, 
    0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x7, 0xf, 0x113, 0xa, 0xf, 0xc, 0xf, 0xe, 
    0xf, 0x116, 0xb, 0xf, 0x3, 0xf, 0x5, 0xf, 0x119, 0xa, 0xf, 0x3, 0xf, 
    0x3, 0xf, 0x3, 0x10, 0x3, 0x10, 0x5, 0x10, 0x11f, 0xa, 0x10, 0x3, 0x11, 
    0x5, 0x11, 0x122, 0xa, 0x11, 0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 0x7, 0x11, 
    0x127, 0xa, 0x11, 0xc, 0x11, 0xe, 0x11, 0x12a, 0xb, 0x11, 0x3, 0x11, 
    0x5, 0x11, 0x12d, 0xa, 0x11, 0x3, 0x12, 0x3, 0x12, 0x3, 0x12, 0x3, 0x12, 
    0x7, 0x12, 0x133, 0xa, 0x12, 0xc, 0x12, 0xe, 0x12, 0x136, 0xb, 0x12, 
    0x3, 0x12, 0x5, 0x12, 0x139, 0xa, 0x12, 0x3, 0x12, 0x3, 0x12, 0x3, 0x13, 
    0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 
    0x15, 0x3, 0x15, 0x3, 0x15, 0x5, 0x15, 0x147, 0xa, 0x15, 0x3, 0x16, 
    0x3, 0x16, 0x3, 0x16, 0x3, 0x16, 0x3, 0x16, 0x3, 0x17, 0x3, 0x17, 0x3, 
    0x17, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 0x3, 0x19, 0x3, 0x19, 
    0x3, 0x19, 0x3, 0x1a, 0x3, 0x1a, 0x3, 0x1a, 0x3, 0x1a, 0x3, 0x1b, 0x3, 
    0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x7, 0x1b, 0x160, 0xa, 0x1b, 0xc, 0x1b, 
    0xe, 0x1b, 0x163, 0xb, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x5, 0x1b, 0x167, 
    0xa, 0x1b, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x5, 0x1c, 0x1a3, 0xa, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x5, 0x1c, 0x1b3, 
    0xa, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x7, 0x1c, 0x1b8, 0xa, 0x1c, 
    0xc, 0x1c, 0xe, 0x1c, 0x1bb, 0xb, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x5, 0x1c, 0x1d2, 
    0xa, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1c, 0x7, 0x1c, 0x201, 0xa, 0x1c, 0xc, 0x1c, 0xe, 0x1c, 0x204, 0xb, 
    0x1c, 0x3, 0x1d, 0x3, 0x1d, 0x3, 0x1d, 0x7, 0x1d, 0x209, 0xa, 0x1d, 
    0xc, 0x1d, 0xe, 0x1d, 0x20c, 0xb, 0x1d, 0x3, 0x1d, 0x5, 0x1d, 0x20f, 
    0xa, 0x1d, 0x3, 0x1e, 0x3, 0x1e, 0x3, 0x1e, 0x3, 0x1e, 0x3, 0x1f, 0x3, 
    0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x7, 0x1f, 
    0x21c, 0xa, 0x1f, 0xc, 0x1f, 0xe, 0x1f, 0x21f, 0xb, 0x1f, 0x3, 0x1f, 
    0x3, 0x1f, 0x5, 0x1f, 0x223, 0xa, 0x1f, 0x3, 0x20, 0x3, 0x20, 0x3, 0x20, 
    0x7, 0x20, 0x228, 0xa, 0x20, 0xc, 0x20, 0xe, 0x20, 0x22b, 0xb, 0x20, 
    0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x7, 0x21, 0x231, 0xa, 0x21, 
    0xc, 0x21, 0xe, 0x21, 0x234, 0xb, 0x21, 0x5, 0x21, 0x236, 0xa, 0x21, 
    0x3, 0x21, 0x3, 0x21, 0x3, 0x22, 0x3, 0x22, 0x3, 0x22, 0x3, 0x22, 0x3, 
    0x22, 0x3, 0x22, 0x7, 0x22, 0x240, 0xa, 0x22, 0xc, 0x22, 0xe, 0x22, 
    0x243, 0xb, 0x22, 0x3, 0x22, 0x3, 0x22, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 
    0x3, 0x23, 0x3, 0x24, 0x3, 0x24, 0x3, 0x24, 0x7, 0x24, 0x24e, 0xa, 0x24, 
    0xc, 0x24, 0xe, 0x24, 0x251, 0xb, 0x24, 0x3, 0x24, 0x2, 0x4, 0x14, 0x36, 
    0x25, 0x2, 0x4, 0x6, 0x8, 0xa, 0xc, 0xe, 0x10, 0x12, 0x14, 0x16, 0x18, 
    0x1a, 0x1c, 0x1e, 0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x2c, 0x2e, 0x30, 
    0x32, 0x34, 0x36, 0x38, 0x3a, 0x3c, 0x3e, 0x40, 0x42, 0x44, 0x46, 0x2, 
    0xc, 0x3, 0x2, 0x2b, 0x2c, 0x4, 0x2, 0x34, 0x34, 0x53, 0x54, 0x3, 0x2, 
    0x43, 0x44, 0x3, 0x2, 0x36, 0x37, 0x3, 0x2, 0x2d, 0x32, 0x3, 0x2, 0x4c, 
    0x4d, 0x3, 0x2, 0x3f, 0x41, 0x3, 0x2, 0x42, 0x43, 0x3, 0x2, 0x3b, 0x3e, 
    0x3, 0x2, 0x4a, 0x4b, 0x2, 0x291, 0x2, 0x4c, 0x3, 0x2, 0x2, 0x2, 0x4, 
    0x54, 0x3, 0x2, 0x2, 0x2, 0x6, 0x61, 0x3, 0x2, 0x2, 0x2, 0x8, 0x9b, 
    0x3, 0x2, 0x2, 0x2, 0xa, 0x9d, 0x3, 0x2, 0x2, 0x2, 0xc, 0xa2, 0x3, 0x2, 
    0x2, 0x2, 0xe, 0xb0, 0x3, 0x2, 0x2, 0x2, 0x10, 0xc3, 0x3, 0x2, 0x2, 
    0x2, 0x12, 0xd1, 0x3, 0x2, 0x2, 0x2, 0x14, 0xe8, 0x3, 0x2, 0x2, 0x2, 
    0x16, 0xf2, 0x3, 0x2, 0x2, 0x2, 0x18, 0x106, 0x3, 0x2, 0x2, 0x2, 0x1a, 
    0x10b, 0x3, 0x2, 0x2, 0x2, 0x1c, 0x118, 0x3, 0x2, 0x2, 0x2, 0x1e, 0x11e, 
    0x3, 0x2, 0x2, 0x2, 0x20, 0x12c, 0x3, 0x2, 0x2, 0x2, 0x22, 0x12e, 0x3, 
    0x2, 0x2, 0x2, 0x24, 0x13c, 0x3, 0x2, 0x2, 0x2, 0x26, 0x140, 0x3, 0x2, 
    0x2, 0x2, 0x28, 0x146, 0x3, 0x2, 0x2, 0x2, 0x2a, 0x148, 0x3, 0x2, 0x2, 
    0x2, 0x2c, 0x14d, 0x3, 0x2, 0x2, 0x2, 0x2e, 0x150, 0x3, 0x2, 0x2, 0x2, 
    0x30, 0x154, 0x3, 0x2, 0x2, 0x2, 0x32, 0x157, 0x3, 0x2, 0x2, 0x2, 0x34, 
    0x166, 0x3, 0x2, 0x2, 0x2, 0x36, 0x1d1, 0x3, 0x2, 0x2, 0x2, 0x38, 0x205, 
    0x3, 0x2, 0x2, 0x2, 0x3a, 0x210, 0x3, 0x2, 0x2, 0x2, 0x3c, 0x222, 0x3, 
    0x2, 0x2, 0x2, 0x3e, 0x224, 0x3, 0x2, 0x2, 0x2, 0x40, 0x22c, 0x3, 0x2, 
    0x2, 0x2, 0x42, 0x239, 0x3, 0x2, 0x2, 0x2, 0x44, 0x246, 0x3, 0x2, 0x2, 
    0x2, 0x46, 0x24a, 0x3, 0x2, 0x2, 0x2, 0x48, 0x4b, 0x5, 0x8, 0x5, 0x2, 
    0x49, 0x4b, 0x5, 0x28, 0x15, 0x2, 0x4a, 0x48, 0x3, 0x2, 0x2, 0x2, 0x4a, 
    0x49, 0x3, 0x2, 0x2, 0x2, 0x4b, 0x4e, 0x3, 0x2, 0x2, 0x2, 0x4c, 0x4a, 
    0x3, 0x2, 0x2, 0x2, 0x4c, 0x4d, 0x3, 0x2, 0x2, 0x2, 0x4d, 0x4f, 0x3, 
    0x2, 0x2, 0x2, 0x4e, 0x4c, 0x3, 0x2, 0x2, 0x2, 0x4f, 0x50, 0x7, 0x2, 
    0x2, 0x3, 0x50, 0x3, 0x3, 0x2, 0x2, 0x2, 0x51, 0x53, 0x5, 0x6, 0x4, 
    0x2, 0x52, 0x51, 0x3, 0x2, 0x2, 0x2, 0x53, 0x56, 0x3, 0x2, 0x2, 0x2, 
    0x54, 0x52, 0x3, 0x2, 0x2, 0x2, 0x54, 0x55, 0x3, 0x2, 0x2, 0x2, 0x55, 
    0x57, 0x3, 0x2, 0x2, 0x2, 0x56, 0x54, 0x3, 0x2, 0x2, 0x2, 0x57, 0x58, 
    0x7, 0x2, 0x2, 0x3, 0x58, 0x5, 0x3, 0x2, 0x2, 0x2, 0x59, 0x5e, 0x5, 
    0x36, 0x1c, 0x2, 0x5a, 0x5b, 0x7, 0x50, 0x2, 0x2, 0x5b, 0x5d, 0x5, 0x36, 
    0x1c, 0x2, 0x5c, 0x5a, 0x3, 0x2, 0x2, 0x2, 0x5d, 0x60, 0x3, 0x2, 0x2, 
    0x2, 0x5e, 0x5c, 0x3, 0x2, 0x2, 0x2, 0x5e, 0x5f, 0x3, 0x2, 0x2, 0x2, 
    0x5f, 0x62, 0x3, 0x2, 0x2, 0x2, 0x60, 0x5e, 0x3, 0x2, 0x2, 0x2, 0x61, 
    0x59, 0x3, 0x2, 0x2, 0x2, 0x61, 0x62, 0x3, 0x2, 0x2, 0x2, 0x62, 0x63, 
    0x3, 0x2, 0x2, 0x2, 0x63, 0x64, 0x7, 0x4f, 0x2, 0x2, 0x64, 0x7, 0x3, 
    0x2, 0x2, 0x2, 0x65, 0x67, 0x5, 0xc, 0x7, 0x2, 0x66, 0x68, 0x7, 0x3, 
    0x2, 0x2, 0x67, 0x66, 0x3, 0x2, 0x2, 0x2, 0x67, 0x68, 0x3, 0x2, 0x2, 
    0x2, 0x68, 0x9c, 0x3, 0x2, 0x2, 0x2, 0x69, 0x6b, 0x5, 0x26, 0x14, 0x2, 
    0x6a, 0x69, 0x3, 0x2, 0x2, 0x2, 0x6b, 0x6e, 0x3, 0x2, 0x2, 0x2, 0x6c, 
    0x6a, 0x3, 0x2, 0x2, 0x2, 0x6c, 0x6d, 0x3, 0x2, 0x2, 0x2, 0x6d, 0x6f, 
    0x3, 0x2, 0x2, 0x2, 0x6e, 0x6c, 0x3, 0x2, 0x2, 0x2, 0x6f, 0x70, 0x9, 
    0x2, 0x2, 0x2, 0x70, 0x71, 0x7, 0x54, 0x2, 0x2, 0x71, 0x73, 0x5, 0x12, 
    0xa, 0x2, 0x72, 0x74, 0x7, 0x3, 0x2, 0x2, 0x73, 0x72, 0x3, 0x2, 0x2, 
    0x2, 0x73, 0x74, 0x3, 0x2, 0x2, 0x2, 0x74, 0x9c, 0x3, 0x2, 0x2, 0x2, 
    0x75, 0x76, 0x7, 0x4, 0x2, 0x2, 0x76, 0x77, 0x5, 0x1c, 0xf, 0x2, 0x77, 
    0x78, 0x7, 0x4a, 0x2, 0x2, 0x78, 0x7a, 0x5, 0x16, 0xc, 0x2, 0x79, 0x7b, 
    0x7, 0x3, 0x2, 0x2, 0x7a, 0x79, 0x3, 0x2, 0x2, 0x2, 0x7a, 0x7b, 0x3, 
    0x2, 0x2, 0x2, 0x7b, 0x9c, 0x3, 0x2, 0x2, 0x2, 0x7c, 0x7d, 0x7, 0x4, 
    0x2, 0x2, 0x7d, 0x7e, 0x5, 0x1c, 0xf, 0x2, 0x7e, 0x7f, 0x7, 0x4a, 0x2, 
    0x2, 0x7f, 0x87, 0x5, 0x1e, 0x10, 0x2, 0x80, 0x81, 0x7, 0x5, 0x2, 0x2, 
    0x81, 0x82, 0x5, 0x1c, 0xf, 0x2, 0x82, 0x83, 0x7, 0x4a, 0x2, 0x2, 0x83, 
    0x84, 0x5, 0x1e, 0x10, 0x2, 0x84, 0x86, 0x3, 0x2, 0x2, 0x2, 0x85, 0x80, 
    0x3, 0x2, 0x2, 0x2, 0x86, 0x89, 0x3, 0x2, 0x2, 0x2, 0x87, 0x85, 0x3, 
    0x2, 0x2, 0x2, 0x87, 0x88, 0x3, 0x2, 0x2, 0x2, 0x88, 0x8b, 0x3, 0x2, 
    0x2, 0x2, 0x89, 0x87, 0x3, 0x2, 0x2, 0x2, 0x8a, 0x8c, 0x7, 0x3, 0x2, 
    0x2, 0x8b, 0x8a, 0x3, 0x2, 0x2, 0x2, 0x8b, 0x8c, 0x3, 0x2, 0x2, 0x2, 
    0x8c, 0x9c, 0x3, 0x2, 0x2, 0x2, 0x8d, 0x8e, 0x7, 0x6, 0x2, 0x2, 0x8e, 
    0x8f, 0x7, 0x7, 0x2, 0x2, 0x8f, 0x90, 0x5, 0xe, 0x8, 0x2, 0x90, 0x91, 
    0x7, 0x8, 0x2, 0x2, 0x91, 0x93, 0x5, 0x16, 0xc, 0x2, 0x92, 0x94, 0x7, 
    0x3, 0x2, 0x2, 0x93, 0x92, 0x3, 0x2, 0x2, 0x2, 0x93, 0x94, 0x3, 0x2, 
    0x2, 0x2, 0x94, 0x9c, 0x3, 0x2, 0x2, 0x2, 0x95, 0x96, 0x7, 0x6, 0x2, 
    0x2, 0x96, 0x97, 0x7, 0x9, 0x2, 0x2, 0x97, 0x99, 0x5, 0x1c, 0xf, 0x2, 
    0x98, 0x9a, 0x7, 0x3, 0x2, 0x2, 0x99, 0x98, 0x3, 0x2, 0x2, 0x2, 0x99, 
    0x9a, 0x3, 0x2, 0x2, 0x2, 0x9a, 0x9c, 0x3, 0x2, 0x2, 0x2, 0x9b, 0x65, 
    0x3, 0x2, 0x2, 0x2, 0x9b, 0x6c, 0x3, 0x2, 0x2, 0x2, 0x9b, 0x75, 0x3, 
    0x2, 0x2, 0x2, 0x9b, 0x7c, 0x3, 0x2, 0x2, 0x2, 0x9b, 0x8d, 0x3, 0x2, 
    0x2, 0x2, 0x9b, 0x95, 0x3, 0x2, 0x2, 0x2, 0x9c, 0x9, 0x3, 0x2, 0x2, 
    0x2, 0x9d, 0x9e, 0x7, 0x54, 0x2, 0x2, 0x9e, 0x9f, 0x5, 0x10, 0x9, 0x2, 
    0x9f, 0xa0, 0x7, 0x8, 0x2, 0x2, 0xa0, 0xa1, 0x5, 0x16, 0xc, 0x2, 0xa1, 
    0xb, 0x3, 0x2, 0x2, 0x2, 0xa2, 0xa3, 0x7, 0x7, 0x2, 0x2, 0xa3, 0xa4, 
    0x5, 0xa, 0x6, 0x2, 0xa4, 0xa5, 0x7, 0x4a, 0x2, 0x2, 0xa5, 0xad, 0x5, 
    0x36, 0x1c, 0x2, 0xa6, 0xa7, 0x7, 0x5, 0x2, 0x2, 0xa7, 0xa8, 0x5, 0xa, 
    0x6, 0x2, 0xa8, 0xa9, 0x7, 0x4a, 0x2, 0x2, 0xa9, 0xaa, 0x5, 0x36, 0x1c, 
    0x2, 0xaa, 0xac, 0x3, 0x2, 0x2, 0x2, 0xab, 0xa6, 0x3, 0x2, 0x2, 0x2, 
    0xac, 0xaf, 0x3, 0x2, 0x2, 0x2, 0xad, 0xab, 0x3, 0x2, 0x2, 0x2, 0xad, 
    0xae, 0x3, 0x2, 0x2, 0x2, 0xae, 0xd, 0x3, 0x2, 0x2, 0x2, 0xaf, 0xad, 
    0x3, 0x2, 0x2, 0x2, 0xb0, 0xb1, 0x7, 0x54, 0x2, 0x2, 0xb1, 0xb2, 0x5, 
    0x12, 0xa, 0x2, 0xb2, 0xf, 0x3, 0x2, 0x2, 0x2, 0xb3, 0xb4, 0x7, 0xa, 
    0x2, 0x2, 0xb4, 0xb5, 0x7, 0x35, 0x2, 0x2, 0xb5, 0xb6, 0x7, 0x8, 0x2, 
    0x2, 0xb6, 0xbd, 0x5, 0x16, 0xc, 0x2, 0xb7, 0xb8, 0x7, 0xb, 0x2, 0x2, 
    0xb8, 0xb9, 0x7, 0x35, 0x2, 0x2, 0xb9, 0xba, 0x7, 0x8, 0x2, 0x2, 0xba, 
    0xbc, 0x5, 0x16, 0xc, 0x2, 0xbb, 0xb7, 0x3, 0x2, 0x2, 0x2, 0xbc, 0xbf, 
    0x3, 0x2, 0x2, 0x2, 0xbd, 0xbb, 0x3, 0x2, 0x2, 0x2, 0xbd, 0xbe, 0x3, 
    0x2, 0x2, 0x2, 0xbe, 0xc0, 0x3, 0x2, 0x2, 0x2, 0xbf, 0xbd, 0x3, 0x2, 
    0x2, 0x2, 0xc0, 0xc1, 0x7, 0xc, 0x2, 0x2, 0xc1, 0xc4, 0x3, 0x2, 0x2, 
    0x2, 0xc2, 0xc4, 0x3, 0x2, 0x2, 0x2, 0xc3, 0xb3, 0x3, 0x2, 0x2, 0x2, 
    0xc3, 0xc2, 0x3, 0x2, 0x2, 0x2, 0xc4, 0x11, 0x3, 0x2, 0x2, 0x2, 0xc5, 
    0xc6, 0x7, 0xa, 0x2, 0x2, 0xc6, 0xcb, 0x5, 0x16, 0xc, 0x2, 0xc7, 0xc8, 
    0x7, 0xb, 0x2, 0x2, 0xc8, 0xca, 0x5, 0x16, 0xc, 0x2, 0xc9, 0xc7, 0x3, 
    0x2, 0x2, 0x2, 0xca, 0xcd, 0x3, 0x2, 0x2, 0x2, 0xcb, 0xc9, 0x3, 0x2, 
    0x2, 0x2, 0xcb, 0xcc, 0x3, 0x2, 0x2, 0x2, 0xcc, 0xce, 0x3, 0x2, 0x2, 
    0x2, 0xcd, 0xcb, 0x3, 0x2, 0x2, 0x2, 0xce, 0xcf, 0x7, 0xc, 0x2, 0x2, 
    0xcf, 0xd2, 0x3, 0x2, 0x2, 0x2, 0xd0, 0xd2, 0x3, 0x2, 0x2, 0x2, 0xd1, 
    0xc5, 0x3, 0x2, 0x2, 0x2, 0xd1, 0xd0, 0x3, 0x2, 0x2, 0x2, 0xd2, 0x13, 
    0x3, 0x2, 0x2, 0x2, 0xd3, 0xd4, 0x8, 0xb, 0x1, 0x2, 0xd4, 0xd5, 0x7, 
    0xa, 0x2, 0x2, 0xd5, 0xd6, 0x5, 0x16, 0xc, 0x2, 0xd6, 0xd7, 0x7, 0xc, 
    0x2, 0x2, 0xd7, 0xe9, 0x3, 0x2, 0x2, 0x2, 0xd8, 0xe9, 0x7, 0x33, 0x2, 
    0x2, 0xd9, 0xda, 0x7, 0xa, 0x2, 0x2, 0xda, 0xdf, 0x5, 0x16, 0xc, 0x2, 
    0xdb, 0xdc, 0x7, 0xb, 0x2, 0x2, 0xdc, 0xde, 0x5, 0x16, 0xc, 0x2, 0xdd, 
    0xdb, 0x3, 0x2, 0x2, 0x2, 0xde, 0xe1, 0x3, 0x2, 0x2, 0x2, 0xdf, 0xdd, 
    0x3, 0x2, 0x2, 0x2, 0xdf, 0xe0, 0x3, 0x2, 0x2, 0x2, 0xe0, 0xe2, 0x3, 
    0x2, 0x2, 0x2, 0xe1, 0xdf, 0x3, 0x2, 0x2, 0x2, 0xe2, 0xe3, 0x7, 0xc, 
    0x2, 0x2, 0xe3, 0xe5, 0x3, 0x2, 0x2, 0x2, 0xe4, 0xd9, 0x3, 0x2, 0x2, 
    0x2, 0xe4, 0xe5, 0x3, 0x2, 0x2, 0x2, 0xe5, 0xe6, 0x3, 0x2, 0x2, 0x2, 
    0xe6, 0xe7, 0x7, 0x54, 0x2, 0x2, 0xe7, 0xe9, 0x5, 0x18, 0xd, 0x2, 0xe8, 
    0xd3, 0x3, 0x2, 0x2, 0x2, 0xe8, 0xd8, 0x3, 0x2, 0x2, 0x2, 0xe8, 0xe4, 
    0x3, 0x2, 0x2, 0x2, 0xe9, 0xef, 0x3, 0x2, 0x2, 0x2, 0xea, 0xeb, 0xc, 
    0x4, 0x2, 0x2, 0xeb, 0xec, 0x7, 0x54, 0x2, 0x2, 0xec, 0xee, 0x5, 0x18, 
    0xd, 0x2, 0xed, 0xea, 0x3, 0x2, 0x2, 0x2, 0xee, 0xf1, 0x3, 0x2, 0x2, 
    0x2, 0xef, 0xed, 0x3, 0x2, 0x2, 0x2, 0xef, 0xf0, 0x3, 0x2, 0x2, 0x2, 
    0xf0, 0x15, 0x3, 0x2, 0x2, 0x2, 0xf1, 0xef, 0x3, 0x2, 0x2, 0x2, 0xf2, 
    0xf7, 0x5, 0x14, 0xb, 0x2, 0xf3, 0xf4, 0x7, 0x3f, 0x2, 0x2, 0xf4, 0xf6, 
    0x5, 0x14, 0xb, 0x2, 0xf5, 0xf3, 0x3, 0x2, 0x2, 0x2, 0xf6, 0xf9, 0x3, 
    0x2, 0x2, 0x2, 0xf7, 0xf5, 0x3, 0x2, 0x2, 0x2, 0xf7, 0xf8, 0x3, 0x2, 
    0x2, 0x2, 0xf8, 0x17, 0x3, 0x2, 0x2, 0x2, 0xf9, 0xf7, 0x3, 0x2, 0x2, 
    0x2, 0xfa, 0xfb, 0x7, 0xd, 0x2, 0x2, 0xfb, 0x100, 0x5, 0x1a, 0xe, 0x2, 
    0xfc, 0xfd, 0x7, 0xb, 0x2, 0x2, 0xfd, 0xff, 0x5, 0x1a, 0xe, 0x2, 0xfe, 
    0xfc, 0x3, 0x2, 0x2, 0x2, 0xff, 0x102, 0x3, 0x2, 0x2, 0x2, 0x100, 0xfe, 
    0x3, 0x2, 0x2, 0x2, 0x100, 0x101, 0x3, 0x2, 0x2, 0x2, 0x101, 0x103, 
    0x3, 0x2, 0x2, 0x2, 0x102, 0x100, 0x3, 0x2, 0x2, 0x2, 0x103, 0x104, 
    0x7, 0xe, 0x2, 0x2, 0x104, 0x107, 0x3, 0x2, 0x2, 0x2, 0x105, 0x107, 
    0x3, 0x2, 0x2, 0x2, 0x106, 0xfa, 0x3, 0x2, 0x2, 0x2, 0x106, 0x105, 0x3, 
    0x2, 0x2, 0x2, 0x107, 0x19, 0x3, 0x2, 0x2, 0x2, 0x108, 0x10c, 0x7, 0xf, 
    0x2, 0x2, 0x109, 0x10c, 0x5, 0x16, 0xc, 0x2, 0x10a, 0x10c, 0x7, 0x36, 
    0x2, 0x2, 0x10b, 0x108, 0x3, 0x2, 0x2, 0x2, 0x10b, 0x109, 0x3, 0x2, 
    0x2, 0x2, 0x10b, 0x10a, 0x3, 0x2, 0x2, 0x2, 0x10c, 0x1b, 0x3, 0x2, 0x2, 
    0x2, 0x10d, 0x119, 0x7, 0x33, 0x2, 0x2, 0x10e, 0x10f, 0x7, 0xa, 0x2, 
    0x2, 0x10f, 0x114, 0x7, 0x33, 0x2, 0x2, 0x110, 0x111, 0x7, 0xb, 0x2, 
    0x2, 0x111, 0x113, 0x7, 0x33, 0x2, 0x2, 0x112, 0x110, 0x3, 0x2, 0x2, 
    0x2, 0x113, 0x116, 0x3, 0x2, 0x2, 0x2, 0x114, 0x112, 0x3, 0x2, 0x2, 
    0x2, 0x114, 0x115, 0x3, 0x2, 0x2, 0x2, 0x115, 0x117, 0x3, 0x2, 0x2, 
    0x2, 0x116, 0x114, 0x3, 0x2, 0x2, 0x2, 0x117, 0x119, 0x7, 0xc, 0x2, 
    0x2, 0x118, 0x10d, 0x3, 0x2, 0x2, 0x2, 0x118, 0x10e, 0x3, 0x2, 0x2, 
    0x2, 0x118, 0x119, 0x3, 0x2, 0x2, 0x2, 0x119, 0x11a, 0x3, 0x2, 0x2, 
    0x2, 0x11a, 0x11b, 0x7, 0x54, 0x2, 0x2, 0x11b, 0x1d, 0x3, 0x2, 0x2, 
    0x2, 0x11c, 0x11f, 0x5, 0x20, 0x11, 0x2, 0x11d, 0x11f, 0x5, 0x22, 0x12, 
    0x2, 0x11e, 0x11c, 0x3, 0x2, 0x2, 0x2, 0x11e, 0x11d, 0x3, 0x2, 0x2, 
    0x2, 0x11f, 0x1f, 0x3, 0x2, 0x2, 0x2, 0x120, 0x122, 0x7, 0x10, 0x2, 
    0x2, 0x121, 0x120, 0x3, 0x2, 0x2, 0x2, 0x121, 0x122, 0x3, 0x2, 0x2, 
    0x2, 0x122, 0x123, 0x3, 0x2, 0x2, 0x2, 0x123, 0x128, 0x5, 0xe, 0x8, 
    0x2, 0x124, 0x125, 0x7, 0x10, 0x2, 0x2, 0x125, 0x127, 0x5, 0xe, 0x8, 
    0x2, 0x126, 0x124, 0x3, 0x2, 0x2, 0x2, 0x127, 0x12a, 0x3, 0x2, 0x2, 
    0x2, 0x128, 0x126, 0x3, 0x2, 0x2, 0x2, 0x128, 0x129, 0x3, 0x2, 0x2, 
    0x2, 0x129, 0x12d, 0x3, 0x2, 0x2, 0x2, 0x12a, 0x128, 0x3, 0x2, 0x2, 
    0x2, 0x12b, 0x12d, 0x3, 0x2, 0x2, 0x2, 0x12c, 0x121, 0x3, 0x2, 0x2, 
    0x2, 0x12c, 0x12b, 0x3, 0x2, 0x2, 0x2, 0x12d, 0x21, 0x3, 0x2, 0x2, 0x2, 
    0x12e, 0x12f, 0x7, 0x11, 0x2, 0x2, 0x12f, 0x134, 0x5, 0x24, 0x13, 0x2, 
    0x130, 0x131, 0x7, 0x12, 0x2, 0x2, 0x131, 0x133, 0x5, 0x24, 0x13, 0x2, 
    0x132, 0x130, 0x3, 0x2, 0x2, 0x2, 0x133, 0x136, 0x3, 0x2, 0x2, 0x2, 
    0x134, 0x132, 0x3, 0x2, 0x2, 0x2, 0x134, 0x135, 0x3, 0x2, 0x2, 0x2, 
    0x135, 0x138, 0x3, 0x2, 0x2, 0x2, 0x136, 0x134, 0x3, 0x2, 0x2, 0x2, 
    0x137, 0x139, 0x7, 0x12, 0x2, 0x2, 0x138, 0x137, 0x3, 0x2, 0x2, 0x2, 
    0x138, 0x139, 0x3, 0x2, 0x2, 0x2, 0x139, 0x13a, 0x3, 0x2, 0x2, 0x2, 
    0x13a, 0x13b, 0x7, 0x13, 0x2, 0x2, 0x13b, 0x23, 0x3, 0x2, 0x2, 0x2, 
    0x13c, 0x13d, 0x7, 0x54, 0x2, 0x2, 0x13d, 0x13e, 0x7, 0x8, 0x2, 0x2, 
    0x13e, 0x13f, 0x5, 0x16, 0xc, 0x2, 0x13f, 0x25, 0x3, 0x2, 0x2, 0x2, 
    0x140, 0x141, 0x7, 0x14, 0x2, 0x2, 0x141, 0x142, 0x7, 0x54, 0x2, 0x2, 
    0x142, 0x27, 0x3, 0x2, 0x2, 0x2, 0x143, 0x147, 0x5, 0x2a, 0x16, 0x2, 
    0x144, 0x147, 0x5, 0x2c, 0x17, 0x2, 0x145, 0x147, 0x5, 0x2e, 0x18, 0x2, 
    0x146, 0x143, 0x3, 0x2, 0x2, 0x2, 0x146, 0x144, 0x3, 0x2, 0x2, 0x2, 
    0x146, 0x145, 0x3, 0x2, 0x2, 0x2, 0x147, 0x29, 0x3, 0x2, 0x2, 0x2, 0x148, 
    0x149, 0x5, 0x3e, 0x20, 0x2, 0x149, 0x14a, 0x7, 0x15, 0x2, 0x2, 0x14a, 
    0x14b, 0x5, 0x3e, 0x20, 0x2, 0x14b, 0x14c, 0x7, 0x3, 0x2, 0x2, 0x14c, 
    0x2b, 0x3, 0x2, 0x2, 0x2, 0x14d, 0x14e, 0x5, 0x36, 0x1c, 0x2, 0x14e, 
    0x14f, 0x7, 0x3, 0x2, 0x2, 0x14f, 0x2d, 0x3, 0x2, 0x2, 0x2, 0x150, 0x151, 
    0x7, 0x15, 0x2, 0x2, 0x151, 0x152, 0x5, 0x36, 0x1c, 0x2, 0x152, 0x153, 
    0x7, 0x3, 0x2, 0x2, 0x153, 0x2f, 0x3, 0x2, 0x2, 0x2, 0x154, 0x155, 0x7, 
    0x54, 0x2, 0x2, 0x155, 0x156, 0x5, 0x34, 0x1b, 0x2, 0x156, 0x31, 0x3, 
    0x2, 0x2, 0x2, 0x157, 0x158, 0x9, 0x3, 0x2, 0x2, 0x158, 0x159, 0x5, 
    0x18, 0xd, 0x2, 0x159, 0x15a, 0x5, 0x34, 0x1b, 0x2, 0x15a, 0x33, 0x3, 
    0x2, 0x2, 0x2, 0x15b, 0x15c, 0x7, 0xa, 0x2, 0x2, 0x15c, 0x161, 0x5, 
    0x36, 0x1c, 0x2, 0x15d, 0x15e, 0x7, 0xb, 0x2, 0x2, 0x15e, 0x160, 0x5, 
    0x36, 0x1c, 0x2, 0x15f, 0x15d, 0x3, 0x2, 0x2, 0x2, 0x160, 0x163, 0x3, 
    0x2, 0x2, 0x2, 0x161, 0x15f, 0x3, 0x2, 0x2, 0x2, 0x161, 0x162, 0x3, 
    0x2, 0x2, 0x2, 0x162, 0x164, 0x3, 0x2, 0x2, 0x2, 0x163, 0x161, 0x3, 
    0x2, 0x2, 0x2, 0x164, 0x165, 0x7, 0xc, 0x2, 0x2, 0x165, 0x167, 0x3, 
    0x2, 0x2, 0x2, 0x166, 0x15b, 0x3, 0x2, 0x2, 0x2, 0x166, 0x167, 0x3, 
    0x2, 0x2, 0x2, 0x167, 0x35, 0x3, 0x2, 0x2, 0x2, 0x168, 0x169, 0x8, 0x1c, 
    0x1, 0x2, 0x169, 0x1d2, 0x7, 0x4e, 0x2, 0x2, 0x16a, 0x16b, 0x7, 0x16, 
    0x2, 0x2, 0x16b, 0x16c, 0x7, 0xd, 0x2, 0x2, 0x16c, 0x16d, 0x7, 0x54, 
    0x2, 0x2, 0x16d, 0x16e, 0x7, 0xe, 0x2, 0x2, 0x16e, 0x1d2, 0x5, 0x34, 
    0x1b, 0x2, 0x16f, 0x1d2, 0x5, 0x32, 0x1a, 0x2, 0x170, 0x1d2, 0x5, 0x40, 
    0x21, 0x2, 0x171, 0x1d2, 0x5, 0x42, 0x22, 0x2, 0x172, 0x173, 0x7, 0xa, 
    0x2, 0x2, 0x173, 0x174, 0x5, 0x36, 0x1c, 0x2, 0x174, 0x175, 0x7, 0xc, 
    0x2, 0x2, 0x175, 0x1d2, 0x3, 0x2, 0x2, 0x2, 0x176, 0x177, 0x9, 0x4, 
    0x2, 0x2, 0x177, 0x1d2, 0x5, 0x36, 0x1c, 0x25, 0x178, 0x1d2, 0x7, 0x35, 
    0x2, 0x2, 0x179, 0x1d2, 0x7, 0x55, 0x2, 0x2, 0x17a, 0x1d2, 0x9, 0x5, 
    0x2, 0x2, 0x17b, 0x1d2, 0x7, 0x3a, 0x2, 0x2, 0x17c, 0x1d2, 0x7, 0x39, 
    0x2, 0x2, 0x17d, 0x1d2, 0x7, 0x38, 0x2, 0x2, 0x17e, 0x1d2, 0x9, 0x6, 
    0x2, 0x2, 0x17f, 0x180, 0x7, 0x11, 0x2, 0x2, 0x180, 0x181, 0x5, 0x38, 
    0x1d, 0x2, 0x181, 0x182, 0x7, 0x13, 0x2, 0x2, 0x182, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x183, 0x184, 0x7, 0x11, 0x2, 0x2, 0x184, 0x185, 0x5, 0x36, 
    0x1c, 0x2, 0x185, 0x186, 0x7, 0x18, 0x2, 0x2, 0x186, 0x187, 0x5, 0x38, 
    0x1d, 0x2, 0x187, 0x188, 0x7, 0x13, 0x2, 0x2, 0x188, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x189, 0x18a, 0x7, 0x19, 0x2, 0x2, 0x18a, 0x18b, 0x5, 0x36, 
    0x1c, 0x2, 0x18b, 0x18c, 0x7, 0x19, 0x2, 0x2, 0x18c, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x18d, 0x18e, 0x7, 0x1a, 0x2, 0x2, 0x18e, 0x18f, 0x7, 0x11, 
    0x2, 0x2, 0x18f, 0x190, 0x5, 0x36, 0x1c, 0x2, 0x190, 0x191, 0x7, 0x13, 
    0x2, 0x2, 0x191, 0x192, 0x7, 0xd, 0x2, 0x2, 0x192, 0x193, 0x5, 0x16, 
    0xc, 0x2, 0x193, 0x194, 0x7, 0xe, 0x2, 0x2, 0x194, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x195, 0x196, 0x7, 0x29, 0x2, 0x2, 0x196, 0x1d2, 0x5, 0x36, 
    0x1c, 0x10, 0x197, 0x198, 0x7, 0x1b, 0x2, 0x2, 0x198, 0x199, 0x5, 0x36, 
    0x1c, 0x2, 0x199, 0x19a, 0x7, 0x4a, 0x2, 0x2, 0x19a, 0x19b, 0x5, 0x36, 
    0x1c, 0x2, 0x19b, 0x19c, 0x7, 0x1c, 0x2, 0x2, 0x19c, 0x19d, 0x5, 0x36, 
    0x1c, 0xa, 0x19d, 0x1d2, 0x3, 0x2, 0x2, 0x2, 0x19e, 0x19f, 0x9, 0x7, 
    0x2, 0x2, 0x19f, 0x1a2, 0x5, 0x3e, 0x20, 0x2, 0x1a0, 0x1a1, 0x7, 0x8, 
    0x2, 0x2, 0x1a1, 0x1a3, 0x5, 0x3e, 0x20, 0x2, 0x1a2, 0x1a0, 0x3, 0x2, 
    0x2, 0x2, 0x1a2, 0x1a3, 0x3, 0x2, 0x2, 0x2, 0x1a3, 0x1a4, 0x3, 0x2, 
    0x2, 0x2, 0x1a4, 0x1a5, 0x7, 0x3, 0x2, 0x2, 0x1a5, 0x1a6, 0x5, 0x36, 
    0x1c, 0x9, 0x1a6, 0x1d2, 0x3, 0x2, 0x2, 0x2, 0x1a7, 0x1a8, 0x7, 0x1d, 
    0x2, 0x2, 0x1a8, 0x1a9, 0x5, 0x36, 0x1c, 0x2, 0x1a9, 0x1aa, 0x7, 0x1e, 
    0x2, 0x2, 0x1aa, 0x1ab, 0x5, 0x36, 0x1c, 0x2, 0x1ab, 0x1ac, 0x7, 0x1f, 
    0x2, 0x2, 0x1ac, 0x1ad, 0x5, 0x36, 0x1c, 0x8, 0x1ad, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x1ae, 0x1af, 0x7, 0x20, 0x2, 0x2, 0x1af, 0x1b0, 0x5, 0x36, 
    0x1c, 0x2, 0x1b0, 0x1b2, 0x7, 0x18, 0x2, 0x2, 0x1b1, 0x1b3, 0x7, 0x10, 
    0x2, 0x2, 0x1b2, 0x1b1, 0x3, 0x2, 0x2, 0x2, 0x1b2, 0x1b3, 0x3, 0x2, 
    0x2, 0x2, 0x1b3, 0x1b4, 0x3, 0x2, 0x2, 0x2, 0x1b4, 0x1b9, 0x5, 0x44, 
    0x23, 0x2, 0x1b5, 0x1b6, 0x7, 0x10, 0x2, 0x2, 0x1b6, 0x1b8, 0x5, 0x44, 
    0x23, 0x2, 0x1b7, 0x1b5, 0x3, 0x2, 0x2, 0x2, 0x1b8, 0x1bb, 0x3, 0x2, 
    0x2, 0x2, 0x1b9, 0x1b7, 0x3, 0x2, 0x2, 0x2, 0x1b9, 0x1ba, 0x3, 0x2, 
    0x2, 0x2, 0x1ba, 0x1bc, 0x3, 0x2, 0x2, 0x2, 0x1bb, 0x1b9, 0x3, 0x2, 
    0x2, 0x2, 0x1bc, 0x1bd, 0x7, 0x21, 0x2, 0x2, 0x1bd, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x1be, 0x1bf, 0x7, 0x22, 0x2, 0x2, 0x1bf, 0x1c0, 0x5, 0x3c, 
    0x1f, 0x2, 0x1c0, 0x1c1, 0x7, 0x4a, 0x2, 0x2, 0x1c1, 0x1c2, 0x5, 0x36, 
    0x1c, 0x2, 0x1c2, 0x1c3, 0x7, 0x1c, 0x2, 0x2, 0x1c3, 0x1c4, 0x5, 0x36, 
    0x1c, 0x5, 0x1c4, 0x1d2, 0x3, 0x2, 0x2, 0x2, 0x1c5, 0x1c6, 0x7, 0x22, 
    0x2, 0x2, 0x1c6, 0x1c7, 0x5, 0xc, 0x7, 0x2, 0x1c7, 0x1c8, 0x7, 0x1c, 
    0x2, 0x2, 0x1c8, 0x1c9, 0x5, 0x36, 0x1c, 0x4, 0x1c9, 0x1d2, 0x3, 0x2, 
    0x2, 0x2, 0x1ca, 0x1cb, 0x7, 0x23, 0x2, 0x2, 0x1cb, 0x1cc, 0x5, 0x36, 
    0x1c, 0x2, 0x1cc, 0x1cd, 0x7, 0x1e, 0x2, 0x2, 0x1cd, 0x1ce, 0x5, 0x36, 
    0x1c, 0x2, 0x1ce, 0x1cf, 0x7, 0x1f, 0x2, 0x2, 0x1cf, 0x1d0, 0x5, 0x36, 
    0x1c, 0x3, 0x1d0, 0x1d2, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x168, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x16a, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x16f, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x170, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x171, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x172, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x176, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x178, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x179, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x17a, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x17b, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x17c, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x17d, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x17e, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x17f, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x183, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x189, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x18d, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x195, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x197, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x19e, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x1a7, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x1ae, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x1be, 0x3, 0x2, 0x2, 0x2, 0x1d1, 0x1c5, 0x3, 0x2, 
    0x2, 0x2, 0x1d1, 0x1ca, 0x3, 0x2, 0x2, 0x2, 0x1d2, 0x202, 0x3, 0x2, 
    0x2, 0x2, 0x1d3, 0x1d4, 0xc, 0x24, 0x2, 0x2, 0x1d4, 0x1d5, 0x9, 0x8, 
    0x2, 0x2, 0x1d5, 0x201, 0x5, 0x36, 0x1c, 0x25, 0x1d6, 0x1d7, 0xc, 0x23, 
    0x2, 0x2, 0x1d7, 0x1d8, 0x9, 0x9, 0x2, 0x2, 0x1d8, 0x201, 0x5, 0x36, 
    0x1c, 0x24, 0x1d9, 0x1da, 0xc, 0x22, 0x2, 0x2, 0x1da, 0x1db, 0x7, 0x17, 
    0x2, 0x2, 0x1db, 0x201, 0x5, 0x36, 0x1c, 0x22, 0x1dc, 0x1dd, 0xc, 0x21, 
    0x2, 0x2, 0x1dd, 0x1de, 0x9, 0xa, 0x2, 0x2, 0x1de, 0x201, 0x5, 0x36, 
    0x1c, 0x22, 0x1df, 0x1e0, 0xc, 0x20, 0x2, 0x2, 0x1e0, 0x1e1, 0x9, 0xb, 
    0x2, 0x2, 0x1e1, 0x201, 0x5, 0x36, 0x1c, 0x21, 0x1e2, 0x1e3, 0xc, 0x1f, 
    0x2, 0x2, 0x1e3, 0x1e4, 0x7, 0x46, 0x2, 0x2, 0x1e4, 0x201, 0x5, 0x36, 
    0x1c, 0x20, 0x1e5, 0x1e6, 0xc, 0x1e, 0x2, 0x2, 0x1e6, 0x1e7, 0x7, 0x45, 
    0x2, 0x2, 0x1e7, 0x201, 0x5, 0x36, 0x1c, 0x1f, 0x1e8, 0x1e9, 0xc, 0x1d, 
    0x2, 0x2, 0x1e9, 0x1ea, 0x7, 0x48, 0x2, 0x2, 0x1ea, 0x201, 0x5, 0x36, 
    0x1c, 0x1e, 0x1eb, 0x1ec, 0xc, 0x1c, 0x2, 0x2, 0x1ec, 0x1ed, 0x7, 0x47, 
    0x2, 0x2, 0x1ed, 0x201, 0x5, 0x36, 0x1c, 0x1d, 0x1ee, 0x1ef, 0xc, 0xf, 
    0x2, 0x2, 0x1ef, 0x1f0, 0x7, 0x2a, 0x2, 0x2, 0x1f0, 0x201, 0x5, 0x36, 
    0x1c, 0x10, 0x1f1, 0x1f2, 0xc, 0xe, 0x2, 0x2, 0x1f2, 0x1f3, 0x7, 0x25, 
    0x2, 0x2, 0x1f3, 0x201, 0x5, 0x36, 0x1c, 0xe, 0x1f4, 0x1f5, 0xc, 0xd, 
    0x2, 0x2, 0x1f5, 0x1f6, 0x7, 0x26, 0x2, 0x2, 0x1f6, 0x201, 0x5, 0x36, 
    0x1c, 0xd, 0x1f7, 0x1f8, 0xc, 0xc, 0x2, 0x2, 0x1f8, 0x1f9, 0x7, 0x27, 
    0x2, 0x2, 0x1f9, 0x201, 0x5, 0x36, 0x1c, 0xc, 0x1fa, 0x1fb, 0xc, 0xb, 
    0x2, 0x2, 0x1fb, 0x1fc, 0x7, 0x28, 0x2, 0x2, 0x1fc, 0x201, 0x5, 0x36, 
    0x1c, 0xb, 0x1fd, 0x1fe, 0xc, 0x7, 0x2, 0x2, 0x1fe, 0x1ff, 0x7, 0x49, 
    0x2, 0x2, 0x1ff, 0x201, 0x7, 0x54, 0x2, 0x2, 0x200, 0x1d3, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1d6, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1d9, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1dc, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1df, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1e2, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1e5, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1e8, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1eb, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1ee, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1f1, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1f4, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1f7, 0x3, 0x2, 
    0x2, 0x2, 0x200, 0x1fa, 0x3, 0x2, 0x2, 0x2, 0x200, 0x1fd, 0x3, 0x2, 
    0x2, 0x2, 0x201, 0x204, 0x3, 0x2, 0x2, 0x2, 0x202, 0x200, 0x3, 0x2, 
    0x2, 0x2, 0x202, 0x203, 0x3, 0x2, 0x2, 0x2, 0x203, 0x37, 0x3, 0x2, 0x2, 
    0x2, 0x204, 0x202, 0x3, 0x2, 0x2, 0x2, 0x205, 0x20a, 0x5, 0x3a, 0x1e, 
    0x2, 0x206, 0x207, 0x7, 0x12, 0x2, 0x2, 0x207, 0x209, 0x5, 0x3a, 0x1e, 
    0x2, 0x208, 0x206, 0x3, 0x2, 0x2, 0x2, 0x209, 0x20c, 0x3, 0x2, 0x2, 
    0x2, 0x20a, 0x208, 0x3, 0x2, 0x2, 0x2, 0x20a, 0x20b, 0x3, 0x2, 0x2, 
    0x2, 0x20b, 0x20e, 0x3, 0x2, 0x2, 0x2, 0x20c, 0x20a, 0x3, 0x2, 0x2, 
    0x2, 0x20d, 0x20f, 0x7, 0x12, 0x2, 0x2, 0x20e, 0x20d, 0x3, 0x2, 0x2, 
    0x2, 0x20e, 0x20f, 0x3, 0x2, 0x2, 0x2, 0x20f, 0x39, 0x3, 0x2, 0x2, 0x2, 
    0x210, 0x211, 0x7, 0x54, 0x2, 0x2, 0x211, 0x212, 0x7, 0x4a, 0x2, 0x2, 
    0x212, 0x213, 0x5, 0x36, 0x1c, 0x2, 0x213, 0x3b, 0x3, 0x2, 0x2, 0x2, 
    0x214, 0x223, 0x5, 0x36, 0x1c, 0x2, 0x215, 0x216, 0x7, 0xa, 0x2, 0x2, 
    0x216, 0x217, 0x5, 0x36, 0x1c, 0x2, 0x217, 0x218, 0x7, 0xb, 0x2, 0x2, 
    0x218, 0x21d, 0x5, 0x36, 0x1c, 0x2, 0x219, 0x21a, 0x7, 0xb, 0x2, 0x2, 
    0x21a, 0x21c, 0x5, 0x36, 0x1c, 0x2, 0x21b, 0x219, 0x3, 0x2, 0x2, 0x2, 
    0x21c, 0x21f, 0x3, 0x2, 0x2, 0x2, 0x21d, 0x21b, 0x3, 0x2, 0x2, 0x2, 
    0x21d, 0x21e, 0x3, 0x2, 0x2, 0x2, 0x21e, 0x220, 0x3, 0x2, 0x2, 0x2, 
    0x21f, 0x21d, 0x3, 0x2, 0x2, 0x2, 0x220, 0x221, 0x7, 0xc, 0x2, 0x2, 
    0x221, 0x223, 0x3, 0x2, 0x2, 0x2, 0x222, 0x214, 0x3, 0x2, 0x2, 0x2, 
    0x222, 0x215, 0x3, 0x2, 0x2, 0x2, 0x223, 0x3d, 0x3, 0x2, 0x2, 0x2, 0x224, 
    0x229, 0x5, 0x36, 0x1c, 0x2, 0x225, 0x226, 0x7, 0xb, 0x2, 0x2, 0x226, 
    0x228, 0x5, 0x36, 0x1c, 0x2, 0x227, 0x225, 0x3, 0x2, 0x2, 0x2, 0x228, 
    0x22b, 0x3, 0x2, 0x2, 0x2, 0x229, 0x227, 0x3, 0x2, 0x2, 0x2, 0x229, 
    0x22a, 0x3, 0x2, 0x2, 0x2, 0x22a, 0x3f, 0x3, 0x2, 0x2, 0x2, 0x22b, 0x229, 
    0x3, 0x2, 0x2, 0x2, 0x22c, 0x235, 0x7, 0xd, 0x2, 0x2, 0x22d, 0x232, 
    0x5, 0x36, 0x1c, 0x2, 0x22e, 0x22f, 0x7, 0xb, 0x2, 0x2, 0x22f, 0x231, 
    0x5, 0x36, 0x1c, 0x2, 0x230, 0x22e, 0x3, 0x2, 0x2, 0x2, 0x231, 0x234, 
    0x3, 0x2, 0x2, 0x2, 0x232, 0x230, 0x3, 0x2, 0x2, 0x2, 0x232, 0x233, 
    0x3, 0x2, 0x2, 0x2, 0x233, 0x236, 0x3, 0x2, 0x2, 0x2, 0x234, 0x232, 
    0x3, 0x2, 0x2, 0x2, 0x235, 0x22d, 0x3, 0x2, 0x2, 0x2, 0x235, 0x236, 
    0x3, 0x2, 0x2, 0x2, 0x236, 0x237, 0x3, 0x2, 0x2, 0x2, 0x237, 0x238, 
    0x7, 0xe, 0x2, 0x2, 0x238, 0x41, 0x3, 0x2, 0x2, 0x2, 0x239, 0x23a, 0x7, 
    0xa, 0x2, 0x2, 0x23a, 0x23b, 0x5, 0x36, 0x1c, 0x2, 0x23b, 0x23c, 0x7, 
    0xb, 0x2, 0x2, 0x23c, 0x241, 0x5, 0x36, 0x1c, 0x2, 0x23d, 0x23e, 0x7, 
    0xb, 0x2, 0x2, 0x23e, 0x240, 0x5, 0x36, 0x1c, 0x2, 0x23f, 0x23d, 0x3, 
    0x2, 0x2, 0x2, 0x240, 0x243, 0x3, 0x2, 0x2, 0x2, 0x241, 0x23f, 0x3, 
    0x2, 0x2, 0x2, 0x241, 0x242, 0x3, 0x2, 0x2, 0x2, 0x242, 0x244, 0x3, 
    0x2, 0x2, 0x2, 0x243, 0x241, 0x3, 0x2, 0x2, 0x2, 0x244, 0x245, 0x7, 
    0xc, 0x2, 0x2, 0x245, 0x43, 0x3, 0x2, 0x2, 0x2, 0x246, 0x247, 0x5, 0x46, 
    0x24, 0x2, 0x247, 0x248, 0x7, 0x24, 0x2, 0x2, 0x248, 0x249, 0x5, 0x36, 
    0x1c, 0x2, 0x249, 0x45, 0x3, 0x2, 0x2, 0x2, 0x24a, 0x24f, 0x5, 0x36, 
    0x1c, 0x2, 0x24b, 0x24c, 0x7, 0x10, 0x2, 0x2, 0x24c, 0x24e, 0x5, 0x36, 
    0x1c, 0x2, 0x24d, 0x24b, 0x3, 0x2, 0x2, 0x2, 0x24e, 0x251, 0x3, 0x2, 
    0x2, 0x2, 0x24f, 0x24d, 0x3, 0x2, 0x2, 0x2, 0x24f, 0x250, 0x3, 0x2, 
    0x2, 0x2, 0x250, 0x47, 0x3, 0x2, 0x2, 0x2, 0x251, 0x24f, 0x3, 0x2, 0x2, 
    0x2, 0x37, 0x4a, 0x4c, 0x54, 0x5e, 0x61, 0x67, 0x6c, 0x73, 0x7a, 0x87, 
    0x8b, 0x93, 0x99, 0x9b, 0xad, 0xbd, 0xc3, 0xcb, 0xd1, 0xdf, 0xe4, 0xe8, 
    0xef, 0xf7, 0x100, 0x106, 0x10b, 0x114, 0x118, 0x11e, 0x121, 0x128, 
    0x12c, 0x134, 0x138, 0x146, 0x161, 0x166, 0x1a2, 0x1b2, 0x1b9, 0x1d1, 
    0x200, 0x202, 0x20a, 0x20e, 0x21d, 0x222, 0x229, 0x232, 0x235, 0x241, 
    0x24f, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

FormulogParser::Initializer FormulogParser::_init;
