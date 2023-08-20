package edu.harvard.seas.pl.formulog.parsing;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import edu.harvard.seas.pl.formulog.ast.BoolTerm;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.NestedFunctionDef;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogBaseVisitor;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.BinopFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.BinopTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ConsTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.DoubleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FloatTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FoldTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FormulaTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FunDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.HoleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.I32TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.I64TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IfExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IndexedFunctorContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IteTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.LetExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.LetFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.LetFunExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ListTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.MatchClauseContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.MatchExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.NonEmptyTermListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.NotFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.OutermostCtorContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ParensTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.QuantifiedFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordEntryContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordUpdateTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.SpecialFPTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.StringTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TermSymFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TupleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UnopTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.VarTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogVisitor;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamKind;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.StackMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class TermExtractor {

  private final ParsingContext pc;
  private final StackMap<String, Identifier> env = new StackMap<>();

  public TermExtractor(ParsingContext parsingContext) {
    pc = parsingContext;
    env.push(new HashMap<>());
  }

  public synchronized Term extract(TermContext ctx) {
    try {
      Term t = visitor.visit(ctx);
      return t;
    } catch (UncheckedParseException e) {
      throw e;
    } catch (Exception e) {
      throw new UncheckedParseException(ctx.start.getLine(), e.getMessage());
    }
  }

  public synchronized List<Term> extractList(List<TermContext> ctxs) {
    List<Term> terms = new ArrayList<>();
    for (TermContext ctx : ctxs) {
      terms.add(extract(ctx));
    }
    return terms;
  }

  public synchronized Term[] extractArray(List<TermContext> ctxs) {
    Term[] terms = new Term[ctxs.size()];
    int i = 0;
    for (TermContext ctx : ctxs) {
      terms[i] = visitor.visit(ctx);
      i++;
    }
    return terms;
  }

  public synchronized void pushIds(Map<String, Identifier> ids) {
    env.push(ids);
  }

  public synchronized Map<String, Identifier> popIds() {
    return env.pop();
  }

  private final FormulogVisitor<Term> visitor =
      new FormulogBaseVisitor<Term>() {

        private boolean inFormula;
        private boolean inPattern;

        private void assertNotInFormula(int lineNo, String msg) {
          if (inFormula) {
            throw new UncheckedParseException(lineNo, msg);
          }
        }

        private void toggleInFormula() {
          inFormula = !inFormula;
        }

        @Override
        public Term visitHoleTerm(HoleTermContext ctx) {
          return Var.makeHole();
        }

        @Override
        public Term visitVarTerm(VarTermContext ctx) {
          String name = ctx.VAR().getText();
          Identifier id = env.get(name);
          if (id == null) {
            id = Identifier.make(Var.fresh(name));
            env.put(name, id);
          }
          assert id.isVar();
          return id.asVar();
        }

        @Override
        public Term visitStringTerm(StringTermContext ctx) {
          String s = ctx.QSTRING().getText();
          return StringTerm.make(s.substring(1, s.length() - 1));
        }

        @Override
        public Term visitConsTerm(ConsTermContext ctx) {
          Term[] args = extractArray(ctx.term());
          return Constructors.make(BuiltInConstructorSymbol.CONS, args);
        }

        private boolean isSpecialFormulaCtor(String name) {
          if (pc.symbolManager().hasName(name)) {
            Symbol sym = pc.symbolManager().lookupSymbol(name);
            return sym instanceof ConstructorSymbol
                && isSpecialFormulaCtor((ConstructorSymbol) sym);
          }
          return false;
        }

        // For a couple constructors, we want to make sure that their arguments are
        // forced to be non-formula types. For example, the constructor bv_const needs
        // to take something of type i32, not i32 smt.
        private boolean isSpecialFormulaCtor(ConstructorSymbol sym) {
          if (sym instanceof ParameterizedConstructorSymbol) {
            switch (((ParameterizedConstructorSymbol) sym).getBase()) {
              case BV_BIG_CONST:
              case BV_CONST:
              case BV_EXTRACT:
              case FP_BIG_CONST:
              case FP_CONST:
                return true;
              default:
                break;
            }
          } else if (sym instanceof BuiltInConstructorSymbol) {
            switch ((BuiltInConstructorSymbol) sym) {
              case INT_BIG_CONST:
              case INT_CONST:
                return true;
              default:
                break;
            }
          }
          return false;
        }

        @Override
        public Term visitIndexedFunctor(IndexedFunctorContext ctx) {
          String name = ctx.id.getText();
          if (name.equals("true") || name.equals("false")) {
            return parseBool(ctx);
          }
          boolean wasInFormula = inFormula;
          boolean isSpecial = isSpecialFormulaCtor(name);
          if (isSpecial) {
            inFormula = false;
          }
          List<Param> params = ParsingUtil.extractParams(pc, ctx.parameterList());
          Term[] args = extractArray(ctx.termArgs().term());
          if (inPattern
              && args.length == 0
              && !pc.symbolManager().hasConstructorSymbolWithName(name)) {
            Var x = Var.fresh(name);
            env.put(name, Identifier.make(x));
          }
          Identifier id = env.get(name);
          if (id != null && id.isVar()) {
            if (args.length > 0) {
              throw new UncheckedParseException(
                  ctx.start.getLine(), "Cannot apply a variable " + name + " to arguments.");
            }
            return id.asVar();
          }
          if (name.charAt(0) == '#' && args.length == 0) {
            if (params.size() != 1) {
              throw new IllegalArgumentException(
                  "Expected a single parameter to solver variable: " + name);
            }
            Type ty = params.get(0).getType();
            return extractSolverSymbol(StringTerm.make(name.substring(1)), ty);
          }
          Symbol sym = id != null ? id.asFunctionSymbol() : pc.symbolManager().lookupSymbol(name);
          if (sym instanceof ParameterizedSymbol) {
            sym = ((ParameterizedSymbol) sym).copyWithNewArgs(params);
          } else if (!params.isEmpty()) {
            throw new UncheckedParseException(
                ctx.start.getLine(), "Symbol " + sym + " is not parametric.");
          }
          adjustFunctorArgs(sym, args);
          Term t = makeFunctor(ctx.start.getLine(), sym, args);
          if (isSpecial) {
            t = makeExitFormula(t);
          }
          inFormula = wasInFormula;
          return t;
        }

        private void adjustFunctorArgs(Symbol sym, Term[] args) {
          if (sym instanceof ParameterizedConstructorSymbol) {
            switch (((ParameterizedConstructorSymbol) sym).getBase()) {
              case BV_EXTRACT:
                args[0] = makeEnterFormula(args[0]);
                break;
              default:
                break;
            }
          }
        }

        private Term parseBool(IndexedFunctorContext ctx) {
          String name = ctx.id.getText();
          assert name.equals("true") || name.equals("false");
          boolean val = name.equals("true");
          if (!ctx.parameterList().parameter().isEmpty()) {
            throw new UncheckedParseException(
                ctx.start.getLine(), "Boolean value " + val + " cannot be parameterized");
          }
          if (!ctx.termArgs().term().isEmpty()) {
            throw new UncheckedParseException(
                ctx.start.getLine(), "Boolean value " + val + " cannot be applied to arguments");
          }
          return BoolTerm.mk(val);
        }

        private Term makeFunctor(int lineNo, Symbol sym, Term[] args) {
          if (sym.getArity() != args.length) {
            throw new UncheckedParseException(
                lineNo,
                "Symbol "
                    + sym
                    + " has arity "
                    + sym.getArity()
                    + ", but applied to "
                    + args.length
                    + " arg(s): "
                    + Arrays.toString(args));
          }
          if (sym instanceof RelationSymbol) {
            FunctionSymbol newSym =
                pc.symbolManager().createPredicateFunctionSymbolPlaceholder((RelationSymbol) sym);
            return pc.functionCallFactory().make(newSym, args);
          } else if (sym instanceof FunctionSymbol) {
            Term t = pc.functionCallFactory().make((FunctionSymbol) sym, args);
            if (sym.getArity() > 0) {
              assertNotInFormula(
                  lineNo, "Cannot invoke a non-nullary function from within a formula: " + t);
            }
            return t;
          } else if (sym instanceof ConstructorSymbol) {
            ConstructorSymbol csym = (ConstructorSymbol) sym;
            Term t = Constructors.make(csym, args);
            return t;
          } else {
            throw new UncheckedParseException(
                lineNo,
                "Cannot create a term with non-constructor, non-function symbol " + sym + ".");
          }
        }

        @Override
        public Term visitFoldTerm(FoldTermContext ctx) {
          assertNotInFormula(
              ctx.start.getLine(), "Cannot invoke a fold from within a formula: " + ctx.getText());
          String name = ctx.ID().getText();
          Identifier id = env.get(name);
          if (id != null && id.isVar()) {
            throw new UncheckedParseException(
                ctx.start.getLine(), "Cannot use a variable as the function to fold: " + name);
          }
          Symbol sym = id != null ? id.asFunctionSymbol() : pc.symbolManager().lookupSymbol(name);
          if (!(sym instanceof FunctionSymbol)) {
            throw new UncheckedParseException(
                ctx.start.getLine(), "Cannot fold over non-function: " + sym);
          }
          if (sym.getArity() != 2) {
            throw new UncheckedParseException(
                ctx.start.getLine(),
                "Can only fold over a binary function, but "
                    + sym
                    + " has arity "
                    + sym.getArity());
          }
          Term[] args = extractArray(ctx.termArgs().term());
          return Fold.mk((FunctionSymbol) sym, args, pc.functionCallFactory());
        }

        @Override
        public Term visitTupleTerm(TupleTermContext ctx) {
          Term[] args = extractArray(ctx.tuple().term());
          return Constructors.make(GlobalSymbolManager.lookupTupleSymbol(args.length), args);
        }

        private final Pattern hex = Pattern.compile("0x([0-9a-fA-F]+)[lL]?");

        @Override
        public Term visitI32Term(I32TermContext ctx) {
          Matcher m = hex.matcher(ctx.val.getText());
          int n;
          if (m.matches()) {
            n = Integer.parseUnsignedInt(m.group(1).toUpperCase(), 16);
          } else {
            n = Integer.parseInt(ctx.val.getText());
          }
          return I32.make(n);
        }

        @Override
        public Term visitI64Term(I64TermContext ctx) {
          Matcher m = hex.matcher(ctx.val.getText());
          long n;
          if (m.matches()) {
            n = Long.parseUnsignedLong(m.group(1).toUpperCase(), 16);
          } else {
            // Long.parseLong does not allow trailing l or L.
            String text = ctx.val.getText();
            String sub = text.substring(0, text.length() - 1);
            n = Long.parseLong(sub);
          }
          return I64.make(n);
        }

        @Override
        public Term visitFloatTerm(FloatTermContext ctx) {
          return FP32.make(Float.parseFloat(ctx.val.getText()));
        }

        @Override
        public Term visitDoubleTerm(DoubleTermContext ctx) {
          return FP64.make(Double.parseDouble(ctx.val.getText()));
        }

        @Override
        public Term visitSpecialFPTerm(SpecialFPTermContext ctx) {
          switch (ctx.val.getType()) {
            case FormulogParser.FP32_NAN:
              return FP32.make(Float.NaN);
            case FormulogParser.FP32_NEG_INFINITY:
              return FP32.make(Float.NEGATIVE_INFINITY);
            case FormulogParser.FP32_POS_INFINITY:
              return FP32.make(Float.POSITIVE_INFINITY);
            case FormulogParser.FP64_NAN:
              return FP64.make(Double.NaN);
            case FormulogParser.FP64_NEG_INFINITY:
              return FP64.make(Double.NEGATIVE_INFINITY);
            case FormulogParser.FP64_POS_INFINITY:
              return FP64.make(Double.POSITIVE_INFINITY);
          }
          throw new AssertionError();
        }

        @Override
        public Term visitRecordTerm(RecordTermContext ctx) {
          Pair<ConstructorSymbol, Map<Integer, Term>> p =
              handleRecordEntries(ctx.recordEntries().recordEntry());
          ConstructorSymbol csym = p.fst();
          Map<Integer, Term> argMap = p.snd();
          Term[] args = new Term[csym.getArity()];
          if (args.length != argMap.keySet().size()) {
            throw new UncheckedParseException(
                ctx.start.getLine(), "Missing label(s) when creating record of type " + csym);
          }
          for (int i = 0; i < args.length; i++) {
            args[i] = argMap.get(i);
          }
          return Constructors.make(csym, args);
        }

        @Override
        public Term visitRecordUpdateTerm(RecordUpdateTermContext ctx) {
          Pair<ConstructorSymbol, Map<Integer, Term>> p =
              handleRecordEntries(ctx.recordEntries().recordEntry());
          ConstructorSymbol csym = p.fst();
          Map<Integer, Term> argMap = p.snd();
          Term[] args = new Term[csym.getArity()];
          FunctionSymbol[] labels = pc.constructorLabels().get(csym);
          Term orig = extract(ctx.term());
          for (int i = 0; i < args.length; ++i) {
            Term t = argMap.get(i);
            if (t == null) {
              FunctionSymbol label = labels[i];
              t = pc.functionCallFactory().make(label, Terms.singletonArray(orig));
            }
            args[i] = t;
          }
          return Constructors.make(csym, args);
        }

        private Pair<ConstructorSymbol, Map<Integer, Term>> handleRecordEntries(
            List<RecordEntryContext> entries) {
          AlgebraicDataType type = null;
          Map<Integer, Term> argMap = new HashMap<>();
          for (RecordEntryContext entry : entries) {
            Symbol label = pc.symbolManager().lookupSymbol(entry.ID().getText());
            Pair<AlgebraicDataType, Integer> p = pc.recordLabels().get(label);
            if (p == null) {
              throw new UncheckedParseException(
                  entry.start.getLine(), label + " is not a record label");
            }
            AlgebraicDataType type2 = p.fst();
            if (type == null) {
              type = type2;
            } else if (!type.equals(type2)) {
              throw new UncheckedParseException(
                  entry.start.getLine(),
                  "Cannot use label " + label + " in a record of type " + type);
            }
            if (argMap.putIfAbsent(p.snd(), extract(entry.term())) != null) {
              throw new UncheckedParseException(
                  entry.start.getLine(),
                  "Cannot use the same label " + label + " multiple times when creating a record");
            }
          }
          ConstructorSymbol csym = type.getConstructors().iterator().next().getSymbol();
          return new Pair<>(csym, argMap);
        }

        @Override
        public Term visitUnopTerm(UnopTermContext ctx) {
          Term t = ctx.term().accept(this);
          FunctionSymbol sym = tokenToUnopSym(ctx.op.getType());
          if (sym == null) {
            t = makeNonFunctionUnop(ctx.op.getType(), t);
          } else {
            t = pc.functionCallFactory().make(sym, new Term[] {t});
          }
          if (t == null) {
            throw new AssertionError("Unrecognized unop: " + ctx.getText());
          }
          assertNotInFormula(
              ctx.start.getLine(), "Cannot invoke a unop from within a formula: " + ctx.getText());
          return t;
        }

        private Term makeNonFunctionUnop(int tokenType, Term t) {
          switch (tokenType) {
            case FormulogParser.BANG:
              return pc.functionCallFactory().make(BuiltInFunctionSymbol.BNOT, new Term[] {t});
            default:
              return null;
          }
        }

        private Term makeBoolMatch(Term matchee, Term ifTrue, Term ifFalse) {
          MatchClause matchTrue = MatchClause.make(BoolTerm.mkTrue(), ifTrue);
          MatchClause matchFalse = MatchClause.make(BoolTerm.mkFalse(), ifFalse);
          return MatchExpr.make(matchee, Arrays.asList(matchTrue, matchFalse));
        }

        private FunctionSymbol tokenToUnopSym(int tokenType) {
          switch (tokenType) {
            case FormulogParser.MINUS:
              return BuiltInFunctionSymbol.I32_NEG;
            default:
              return null;
          }
        }

        private FunctionSymbol tokenToBinopSym(int tokenType) {
          switch (tokenType) {
            case FormulogParser.MUL:
              return BuiltInFunctionSymbol.I32_MUL;
            case FormulogParser.DIV:
              return BuiltInFunctionSymbol.I32_SDIV;
            case FormulogParser.REM:
              return BuiltInFunctionSymbol.I32_SREM;
            case FormulogParser.PLUS:
              return BuiltInFunctionSymbol.I32_ADD;
            case FormulogParser.MINUS:
              return BuiltInFunctionSymbol.I32_SUB;
            case FormulogParser.AMP:
              return BuiltInFunctionSymbol.I32_AND;
            case FormulogParser.CARET:
              return BuiltInFunctionSymbol.I32_XOR;
            case FormulogParser.EQ:
              return BuiltInFunctionSymbol.BEQ;
            case FormulogParser.NEQ:
              return BuiltInFunctionSymbol.BNEQ;
            case FormulogParser.LT:
              return BuiltInFunctionSymbol.I32_LT;
            case FormulogParser.LTE:
              return BuiltInFunctionSymbol.I32_LE;
            case FormulogParser.GT:
              return BuiltInFunctionSymbol.I32_GT;
            case FormulogParser.GTE:
              return BuiltInFunctionSymbol.I32_GE;
            default:
              return null;
          }
        }

        private Term makeNonFunctionBinop(int tokenType, Term lhs, Term rhs) {
          switch (tokenType) {
            case FormulogParser.AMPAMP:
              return makeBoolMatch(lhs, rhs, BoolTerm.mkFalse());
            case FormulogParser.BARBAR:
              return makeBoolMatch(lhs, BoolTerm.mkTrue(), rhs);
            default:
              return null;
          }
        }

        @Override
        public Term visitBinopTerm(BinopTermContext ctx) {
          Term[] args = {extract(ctx.term(0)), extract(ctx.term(1))};
          FunctionSymbol sym = tokenToBinopSym(ctx.op.getType());
          Term t;
          if (sym == null) {
            t = makeNonFunctionBinop(ctx.op.getType(), args[0], args[1]);
          } else {
            t = pc.functionCallFactory().make(sym, args);
          }
          if (t == null) {
            throw new AssertionError("Unrecognized binop: " + ctx.getText());
          }
          assertNotInFormula(
              ctx.start.getLine(), "Cannot invoke a binop from within a formula: " + ctx.getText());
          return t;
        }

        @Override
        public Term visitListTerm(ListTermContext ctx) {
          Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
          List<TermContext> ctxs = new ArrayList<>(ctx.list().term());
          Collections.reverse(ctxs);
          for (TermContext tc : ctxs) {
            t = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] {extract(tc), t});
          }
          return t;
        }

        @Override
        public Term visitParensTerm(ParensTermContext ctx) {
          return extract(ctx.term());
        }

        private Term makeExitFormula(Term t) {
          return Constructors.make(BuiltInConstructorSymbol.EXIT_FORMULA, Terms.singletonArray(t));
        }

        private Term makeEnterFormula(Term t) {
          return Constructors.make(BuiltInConstructorSymbol.ENTER_FORMULA, Terms.singletonArray(t));
        }

        @Override
        public Term visitFormulaTerm(FormulaTermContext ctx) {
          assertNotInFormula(
              ctx.start.getLine(), "Cannot nest a formula within a formula: " + ctx.getText());
          toggleInFormula();
          Term t = extract(ctx.term());
          t = makeEnterFormula(t);
          toggleInFormula();
          return t;
        }

        @Override
        public Term visitNotFormula(NotFormulaContext ctx) {
          Term t = extract(ctx.term());
          return Constructors.make(BuiltInConstructorSymbol.SMT_NOT, Terms.singletonArray(t));
        }

        @Override
        public Term visitBinopFormula(BinopFormulaContext ctx) {
          Term[] args = extractArray(ctx.term());
          ConstructorSymbol sym;
          switch (ctx.op.getType()) {
            case FormulogParser.FORMULA_EQ:
            case FormulogParser.IFF:
              sym =
                  (ConstructorSymbol)
                      pc.symbolManager()
                          .getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_EQ);
              break;
            case FormulogParser.IMP:
              sym = BuiltInConstructorSymbol.SMT_IMP;
              break;
            case FormulogParser.AND:
              sym = BuiltInConstructorSymbol.SMT_AND;
              break;
            case FormulogParser.OR:
              sym = BuiltInConstructorSymbol.SMT_OR;
              break;
            default:
              throw new AssertionError();
          }
          return Constructors.make(sym, args);
        }

        @Override
        public Term visitLetFormula(LetFormulaContext ctx) {
          ConstructorSymbol sym =
              (ConstructorSymbol)
                  pc.symbolManager().getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_LET);
          boolean wasInFormula = inFormula;
          inFormula = false;
          Term[] args = extractArray(ctx.term());
          inFormula = wasInFormula;
          args[1] = makeEnterFormula(args[1]);
          args[2] = makeEnterFormula(args[2]);
          return makeExitFormula(Constructors.make(sym, args));
        }

        @Override
        public Term visitQuantifiedFormula(QuantifiedFormulaContext ctx) {
          Term[] args = new Term[3];
          args[0] = parseFormulaVarList(ctx.variables);
          args[1] = makeEnterFormula(extract(ctx.boundTerm));
          args[2] = Constructors.nil();
          if (ctx.pattern != null) {
            args[2] =
                Constructors.make(
                    BuiltInConstructorSymbol.CONS,
                    new Term[] {(parsePatternList(ctx.pattern)), args[2]});
          }
          ConstructorSymbol sym;
          switch (ctx.quantifier.getType()) {
            case FormulogParser.FORALL:
              sym = BuiltInConstructorSymbol.SMT_FORALL;
              break;
            case FormulogParser.EXISTS:
              sym = BuiltInConstructorSymbol.SMT_EXISTS;
              break;
            default:
              throw new AssertionError("impossible");
          }
          return makeExitFormula(Constructors.make(sym, args));
        }

        private Term parsePatternList(NonEmptyTermListContext ctx) {
          return parseNonEmptyTermList(
              ctx,
              pat -> {
                ConstructorSymbol sym =
                    (ConstructorSymbol)
                        pc.symbolManager()
                            .getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_PAT);
                return Constructors.make(sym, Terms.singletonArray(makeEnterFormula(pat)));
              });
        }

        private Term parseFormulaVarList(NonEmptyTermListContext ctx) {
          return parseNonEmptyTermList(
              ctx,
              var -> {
                ConstructorSymbol sym =
                    (ConstructorSymbol)
                        pc.symbolManager()
                            .getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_WRAP_VAR);
                return Constructors.make(sym, Terms.singletonArray(var));
              });
        }

        private Term parseNonEmptyTermList(
            NonEmptyTermListContext ctx, Function<Term, Term> transformer) {
          Term acc = Constructors.nil();
          List<TermContext> ctxs = new ArrayList<>(ctx.term());
          Collections.reverse(ctxs);
          for (TermContext tc : ctxs) {
            Term t = transformer.apply(extract(tc));
            acc = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] {t, acc});
          }
          return acc;
        }

        @Override
        public Term visitIteTerm(IteTermContext ctx) {
          Term[] args = extractArray(ctx.term());
          if (inFormula) {
            return Constructors.make(BuiltInConstructorSymbol.SMT_ITE, args);
          } else {
            return makeBoolMatch(args[0], args[1], args[2]);
          }
        }

        @Override
        public Term visitTermSymFormula(TermSymFormulaContext ctx) {
          Type type = ParsingUtil.extractParam(pc, ctx.parameter()).getType();
          Term id = extract(ctx.term());
          return extractSolverSymbol(id, type);
        }

        private Term extractSolverSymbol(Term id, Type type) {
          ParameterizedConstructorSymbol sym =
              GlobalSymbolManager.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_VAR);
          sym = sym.copyWithNewArgs(Param.wildCard(), new Param(type, ParamKind.PRE_SMT_TYPE));
          return makeExitFormula(Constructors.make(sym, Terms.singletonArray(id)));
        }

        public Term visitOutermostCtor(OutermostCtorContext ctx) {
          Symbol sym = pc.symbolManager().lookupSymbol(ctx.ID().getText());
          if (!(sym instanceof ConstructorSymbol)) {
            throw new UncheckedParseException(
                ctx.start.getLine(),
                "Cannot use non-constructor symbol " + sym + " in a `not` term.");
          }

          Term[] vars = new Term[sym.getArity()];
          for (int i = 0; i < vars.length; ++i) {
            vars[i] = Var.fresh();
          }
          Term pat = Constructors.make((ConstructorSymbol) sym, vars);
          List<MatchClause> clauses = new ArrayList<>();
          clauses.add(MatchClause.make(pat, BoolTerm.mkFalse()));
          clauses.add(MatchClause.make(Var.fresh(), BoolTerm.mkTrue()));
          Term arg = extract(ctx.term());
          return MatchExpr.make(arg, clauses);
        }

        @Override
        public Term visitMatchExpr(MatchExprContext ctx) {
          Term guard = ctx.term().accept(this);
          List<MatchClause> matches = new ArrayList<>();
          for (MatchClauseContext mcc : ctx.matchClause()) {
            for (TermContext pc : mcc.patterns().term()) {
              env.push(new HashMap<>());
              inPattern = true;
              Term pattern = extract(pc);
              inPattern = false;
              Term rhs = extract(mcc.rhs);
              env.pop();
              MatchClause clause = MatchClause.make(pattern, rhs);
              matches.add(clause);
            }
          }
          return MatchExpr.make(guard, matches);
        }

        @Override
        public Term visitLetExpr(LetExprContext ctx) {
          Term assign = ctx.assign.accept(this);
          env.push(new HashMap<>());
          inPattern = true;
          List<Term> ts = new ArrayList<>();
          for (TermContext termCtx : ctx.lhs.term()) {
            ts.add(extract(termCtx));
          }
          Term t;
          if (ts.size() > 1) {
            t =
                Constructors.make(
                    GlobalSymbolManager.lookupTupleSymbol(ts.size()),
                    ts.toArray(Terms.emptyArray()));
          } else {
            t = ts.get(0);
          }
          inPattern = false;
          Term body = ctx.body.accept(this);
          env.pop();

          MatchClause m = MatchClause.make(t, body);
          return MatchExpr.make(assign, Collections.singletonList(m));
        }

        @Override
        public Term visitLetFunExpr(LetFunExprContext ctx) {
          if (inFormula) {
            throw new UncheckedParseException(
                ctx.start.getLine(),
                "Cannot define a function from within a formula:\n" + ctx.getText());
          }
          List<String> names = new ArrayList<>();
          for (FunDefLHSContext f : ctx.funDefs().funDefLHS()) {
            String name = f.ID().getText();
            if (names.contains(name)) {
              throw new UncheckedParseException(
                  ctx.start.getLine(),
                  "Cannot use the same name more than once in a mutually-recursive function"
                      + " definition "
                      + name);
            }
            names.add(name);
          }
          List<Pair<FunctionSymbol, List<Var>>> signatures =
              ParsingUtil.extractFunDeclarations(pc, ctx.funDefs().funDefLHS(), true);
          Iterator<Pair<FunctionSymbol, List<Var>>> sigIt = signatures.iterator();
          HashMap<String, Identifier> m = new HashMap<>();
          for (String name : names) {
            m.put(name, Identifier.make(sigIt.next().fst()));
          }
          env.push(m);
          sigIt = signatures.iterator();
          Set<NestedFunctionDef> defs = new HashSet<>();
          for (TermContext bodyCtx : ctx.funDefs().term()) {
            Pair<FunctionSymbol, List<Var>> p = sigIt.next();
            List<Var> params = p.snd();
            env.push(ParsingUtil.varsToIds(params));
            defs.add(NestedFunctionDef.make(p.fst(), params, extract(bodyCtx)));
            env.pop();
          }
          Term letBody = extract(ctx.letFunBody);
          env.pop();
          return LetFunExpr.make(defs, letBody);
        }

        @Override
        public Term visitIfExpr(IfExprContext ctx) {
          Term guard = ctx.guard.accept(this);
          Term thenExpr = ctx.thenExpr.accept(this);
          Term elseExpr = ctx.elseExpr.accept(this);
          List<MatchClause> branches = new ArrayList<>();
          branches.add(MatchClause.make(BoolTerm.mkTrue(), thenExpr));
          branches.add(MatchClause.make(BoolTerm.mkFalse(), elseExpr));
          return MatchExpr.make(guard, branches);
        }
      };
}
