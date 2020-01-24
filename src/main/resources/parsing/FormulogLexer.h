
// Generated from Formulog.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"




class  FormulogLexer : public antlr4::Lexer {
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

  FormulogLexer(antlr4::CharStream *input);
  ~FormulogLexer();

  virtual std::string getGrammarFileName() const override;
  virtual const std::vector<std::string>& getRuleNames() const override;

  virtual const std::vector<std::string>& getChannelNames() const override;
  virtual const std::vector<std::string>& getModeNames() const override;
  virtual const std::vector<std::string>& getTokenNames() const override; // deprecated, use vocabulary instead
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;

  virtual const std::vector<uint16_t> getSerializedATN() const override;
  virtual const antlr4::atn::ATN& getATN() const override;

private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;
  static std::vector<std::string> _channelNames;
  static std::vector<std::string> _modeNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  // Individual action functions triggered by action() above.

  // Individual semantic predicate functions triggered by sempred() above.

  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

