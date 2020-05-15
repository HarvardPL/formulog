package formulog.parsing;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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

import formulog.ast.BoolTerm;
import formulog.ast.Constructors;
import formulog.ast.FP32;
import formulog.ast.FP64;
import formulog.ast.Fold;
import formulog.ast.I32;
import formulog.ast.I64;
import formulog.ast.LetFunExpr;
import formulog.ast.MatchClause;
import formulog.ast.MatchExpr;
import formulog.ast.NestedFunctionDef;
import formulog.ast.StringTerm;
import formulog.ast.Term;
import formulog.ast.Terms;
import formulog.ast.Var;
import formulog.symbols.BuiltInConstructorSymbol;
import formulog.symbols.BuiltInFunctionSymbol;
import formulog.symbols.ConstructorSymbol;
import formulog.symbols.FunctionSymbol;
import formulog.symbols.GlobalSymbolManager;
import formulog.symbols.RelationSymbol;
import formulog.symbols.Symbol;
import formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import formulog.symbols.parameterized.Param;
import formulog.symbols.parameterized.ParamKind;
import formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import formulog.symbols.parameterized.ParameterizedSymbol;
import formulog.types.Types.AlgebraicDataType;
import formulog.types.Types.Type;
import formulog.util.Pair;
import formulog.util.StackMap;
import formulog.parsing.generated.FormulogBaseVisitor;
import formulog.parsing.generated.FormulogParser;
import formulog.parsing.generated.FormulogVisitor;
import formulog.parsing.generated.FormulogParser.BinopFormulaContext;
import formulog.parsing.generated.FormulogParser.BinopTermContext;
import formulog.parsing.generated.FormulogParser.ConsTermContext;
import formulog.parsing.generated.FormulogParser.DoubleTermContext;
import formulog.parsing.generated.FormulogParser.FloatTermContext;
import formulog.parsing.generated.FormulogParser.FoldTermContext;
import formulog.parsing.generated.FormulogParser.FormulaTermContext;
import formulog.parsing.generated.FormulogParser.FunDefLHSContext;
import formulog.parsing.generated.FormulogParser.HoleTermContext;
import formulog.parsing.generated.FormulogParser.I32TermContext;
import formulog.parsing.generated.FormulogParser.I64TermContext;
import formulog.parsing.generated.FormulogParser.IfExprContext;
import formulog.parsing.generated.FormulogParser.IndexedFunctorContext;
import formulog.parsing.generated.FormulogParser.IteTermContext;
import formulog.parsing.generated.FormulogParser.LetExprContext;
import formulog.parsing.generated.FormulogParser.LetFormulaContext;
import formulog.parsing.generated.FormulogParser.LetFunExprContext;
import formulog.parsing.generated.FormulogParser.ListTermContext;
import formulog.parsing.generated.FormulogParser.MatchClauseContext;
import formulog.parsing.generated.FormulogParser.MatchExprContext;
import formulog.parsing.generated.FormulogParser.NonEmptyTermListContext;
import formulog.parsing.generated.FormulogParser.NotFormulaContext;
import formulog.parsing.generated.FormulogParser.OutermostCtorContext;
import formulog.parsing.generated.FormulogParser.ParensTermContext;
import formulog.parsing.generated.FormulogParser.QuantifiedFormulaContext;
import formulog.parsing.generated.FormulogParser.RecordEntryContext;
import formulog.parsing.generated.FormulogParser.RecordTermContext;
import formulog.parsing.generated.FormulogParser.RecordUpdateTermContext;
import formulog.parsing.generated.FormulogParser.SpecialFPTermContext;
import formulog.parsing.generated.FormulogParser.StringTermContext;
import formulog.parsing.generated.FormulogParser.TermContext;
import formulog.parsing.generated.FormulogParser.TermSymFormulaContext;
import formulog.parsing.generated.FormulogParser.TupleTermContext;
import formulog.parsing.generated.FormulogParser.UnopTermContext;
import formulog.parsing.generated.FormulogParser.VarTermContext;

class TermExtractor {

	private final ParsingContext pc;

	public TermExtractor(ParsingContext parsingContext) {
		pc = parsingContext;
	}

	public synchronized Term extract(TermContext ctx) {
		return visitor.visit(ctx);
	}

	public synchronized List<Term> extractList(List<TermContext> ctxs) {
		List<Term> terms = new ArrayList<>();
		for (TermContext ctx : ctxs) {
			terms.add(visitor.visit(ctx));
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

	private final FormulogVisitor<Term> visitor = new FormulogBaseVisitor<Term>() {

		private boolean inFormula;
		private final StackMap<String, FunctionSymbol> nestedFunctions = new StackMap<>();

		private void assertNotInFormula(String msg) {
			if (inFormula) {
				throw new RuntimeException(msg);
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
			return Var.make(name);
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

		@Override
		public Term visitIndexedFunctor(IndexedFunctorContext ctx) {
			String name = ctx.id.getText();
			if (name.equals("true") || name.equals("false")) {
				return parseBool(ctx);
			}
			List<Param> params = ParsingUtil.extractParams(pc, ctx.parameterList());
			Symbol sym = nestedFunctions.get(name);
			Term[] args = extractArray(ctx.termArgs().term());
			if (name.charAt(0) == '#' && args.length == 0) {
				if (params.size() != 1) {
					throw new IllegalArgumentException("Expected a single parameter to solver variable: " + name);
				}
				Type ty = params.get(0).getType();
				return extractSolverSymbol(StringTerm.make(name.substring(1)), ty);
			}
			if (sym == null) {
				sym = pc.symbolManager().lookupSymbol(name);
			}
			if (sym instanceof ParameterizedSymbol) {
				sym = ((ParameterizedSymbol) sym).copyWithNewArgs(params);
			} else if (!params.isEmpty()) {
				throw new RuntimeException("Symbol " + sym + " is not parametric.");
			}
			Term t = makeFunctor(sym, args);
			// For a couple constructors, we want to make sure that their arguments are
			// forced to be non-formula types. For example, the constructor bv_const needs
			// to take something of type i32, not i32 expr.
			if (sym instanceof ParameterizedConstructorSymbol) {
				switch (((ParameterizedConstructorSymbol) sym).getBase()) {
				case BV_BIG_CONST:
				case BV_CONST:
				case FP_BIG_CONST:
				case FP_CONST:
					t = makeExitFormula(t);
				default:
					break;
				}
			}
			return t;
		}
		
		private Term parseBool(IndexedFunctorContext ctx) {
			String name = ctx.id.getText();
			assert name.equals("true") || name.equals("false");
			boolean val = name.equals("true");
			if (!ctx.parameterList().parameter().isEmpty()) {
				throw new RuntimeException("Boolean value " + val + " cannot be parameterized");
			}
			if (!ctx.termArgs().term().isEmpty()) {
				throw new RuntimeException("Boolean value " + val + " cannot be applied to arguments");
			}
			return BoolTerm.mk(val);
		}

		private Term makeFunctor(Symbol sym, Term[] args) {
			if (sym instanceof RelationSymbol) {
				FunctionSymbol newSym = pc.symbolManager()
						.createPredicateFunctionSymbolPlaceholder((RelationSymbol) sym);
				return pc.functionCallFactory().make(newSym, args);
			} else if (sym instanceof FunctionSymbol) {
				Term t = pc.functionCallFactory().make((FunctionSymbol) sym, args);
				if (sym.getArity() > 0) {
					assertNotInFormula("Cannot invoke a non-nullary function from within a formula: " + t);
				}
				return t;
			} else if (sym instanceof ConstructorSymbol) {
				ConstructorSymbol csym = (ConstructorSymbol) sym;
				Term t = Constructors.make(csym, args);
				return t;
			} else {
				throw new RuntimeException(
						"Cannot create a term with non-constructor, non-function symbol " + sym + ".");
			}
		}

		@Override
		public Term visitFoldTerm(FoldTermContext ctx) {
			assertNotInFormula("Cannot invoke a fold from within a formula: " + ctx.getText());
			String name = ctx.ID().getText();
			Symbol sym = nestedFunctions.get(name);
			if (sym == null) {
				sym = pc.symbolManager().lookupSymbol(name);
			}
			if (!(sym instanceof FunctionSymbol)) {
				throw new RuntimeException("Cannot fold over non-function: " + sym);
			}
			if (sym.getArity() != 2) {
				throw new RuntimeException(
						"Can only fold over a binary function, but " + sym + " has arity " + sym.getArity());
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
			Pair<ConstructorSymbol, Map<Integer, Term>> p = handleRecordEntries(ctx.recordEntries().recordEntry());
			ConstructorSymbol csym = p.fst();
			Map<Integer, Term> argMap = p.snd();
			Term[] args = new Term[csym.getArity()];
			if (args.length != argMap.keySet().size()) {
				throw new RuntimeException("Missing label(s) when creating record of type " + csym);
			}
			for (int i = 0; i < args.length; i++) {
				args[i] = argMap.get(i);
			}
			return Constructors.make(csym, args);
		}

		@Override
		public Term visitRecordUpdateTerm(RecordUpdateTermContext ctx) {
			Pair<ConstructorSymbol, Map<Integer, Term>> p = handleRecordEntries(ctx.recordEntries().recordEntry());
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

		private Pair<ConstructorSymbol, Map<Integer, Term>> handleRecordEntries(List<RecordEntryContext> entries) {
			AlgebraicDataType type = null;
			Map<Integer, Term> argMap = new HashMap<>();
			for (RecordEntryContext entry : entries) {
				Symbol label = pc.symbolManager().lookupSymbol(entry.ID().getText());
				Pair<AlgebraicDataType, Integer> p = pc.recordLabels().get(label);
				if (p == null) {
					throw new RuntimeException(label + " is not a record label");
				}
				AlgebraicDataType type2 = p.fst();
				if (type == null) {
					type = type2;
				} else if (!type.equals(type2)) {
					throw new RuntimeException("Cannot use label " + label + " in a record of type " + type);
				}
				if (argMap.putIfAbsent(p.snd(), extract(entry.term())) != null) {
					throw new RuntimeException(
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
				t = pc.functionCallFactory().make(sym, new Term[] { t });
			}
			if (t == null) {
				throw new AssertionError("Unrecognized unop: " + ctx.getText());
			}
			assertNotInFormula("Cannot invoke a unop from within a formula: " + ctx.getText());
			return t;
		}

		private Term makeNonFunctionUnop(int tokenType, Term t) {
			switch (tokenType) {
			case FormulogParser.BANG:
				return pc.functionCallFactory().make(BuiltInFunctionSymbol.BNOT, new Term[] { t });
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
				return BuiltInFunctionSymbol.I32_DIV;
			case FormulogParser.REM:
				return BuiltInFunctionSymbol.I32_REM;
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
			Term[] args = { extract(ctx.term(0)), extract(ctx.term(1)) };
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
			assertNotInFormula("Cannot invoke a binop from within a formula: " + ctx.getText());
			return t;
		}

		@Override
		public Term visitListTerm(ListTermContext ctx) {
			Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
			List<TermContext> ctxs = new ArrayList<>(ctx.list().term());
			Collections.reverse(ctxs);
			for (TermContext tc : ctxs) {
				t = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { extract(tc), t });
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
			assertNotInFormula("Cannot nest a formula within a formula: " + ctx.getText());
			toggleInFormula();
			Term t = extract(ctx.term());
			t = Constructors.make(BuiltInConstructorSymbol.ENTER_FORMULA, Terms.singletonArray(t));
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
				sym = (ConstructorSymbol) pc.symbolManager()
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
			ConstructorSymbol sym = (ConstructorSymbol) pc.symbolManager()
					.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_LET);
			Term[] args = extractArray(ctx.term());
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
				args[2] = Constructors.make(BuiltInConstructorSymbol.CONS,
						new Term[] { (parsePatternList(ctx.pattern)), args[2] });
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
			return parseNonEmptyTermList(ctx, pat -> {
				ConstructorSymbol sym = (ConstructorSymbol) pc.symbolManager()
						.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_PAT);
				return Constructors.make(sym, Terms.singletonArray(makeEnterFormula(pat)));
			});
		}
		
		private Term parseFormulaVarList(NonEmptyTermListContext ctx) {
			return parseNonEmptyTermList(ctx, var -> {
				ConstructorSymbol sym = (ConstructorSymbol) pc.symbolManager()
						.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_WRAP_VAR);
				return Constructors.make(sym, Terms.singletonArray(var));
			});
		}

		private Term parseNonEmptyTermList(NonEmptyTermListContext ctx, Function<Term, Term> transformer) {
			Term acc = Constructors.nil();
			List<TermContext> ctxs = new ArrayList<>(ctx.term());
			Collections.reverse(ctxs);
			for (TermContext tc : ctxs) {
				Term t = transformer.apply(extract(tc));
				acc = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { t, acc });
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
			ParameterizedConstructorSymbol sym = GlobalSymbolManager.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_VAR);
			sym = sym.copyWithNewArgs(Param.wildCard(), new Param(type, ParamKind.PRE_SMT_TYPE));
			return makeExitFormula(Constructors.make(sym, Terms.singletonArray(id)));
		}

		public Term visitOutermostCtor(OutermostCtorContext ctx) {
			Symbol sym = pc.symbolManager().lookupSymbol(ctx.ID().getText());
			if (!(sym instanceof ConstructorSymbol)) {
				throw new RuntimeException("Cannot use non-constructor symbol " + sym + " in a `not` term.");
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
				Term rhs = extract(mcc.rhs);
				for (TermContext pc : mcc.patterns().term()) {
					Term pattern = extract(pc);
					matches.add(MatchClause.make(pattern, rhs));
				}
			}
			return MatchExpr.make(guard, matches);
		}

		@Override
		public Term visitLetExpr(LetExprContext ctx) {
			List<Term> ts = extractList(ctx.letBind().term());
			Term t;
			if (ts.size() > 1) {
				t = Constructors.make(GlobalSymbolManager.lookupTupleSymbol(ts.size()), ts.toArray(Terms.emptyArray()));
			} else {
				t = ts.get(0);
			}
			Term assign = ctx.assign.accept(this);
			Term body = ctx.body.accept(this);
			MatchClause m = MatchClause.make(t, body);
			return MatchExpr.make(assign, Collections.singletonList(m));
		}

		@Override
		public Term visitLetFunExpr(LetFunExprContext ctx) {
			if (inFormula) {
				throw new RuntimeException("Cannot define a function from within a formula:\n" + ctx.getText());
			}
			List<String> names = new ArrayList<>();
			for (FunDefLHSContext f : ctx.funDefs().funDefLHS()) {
				String name = f.ID().getText();
				if (!names.add(name)) {
					throw new RuntimeException(
							"Cannot use the same name more than once in a mutually-recursive function definition "
									+ name);
				}
			}
			List<Pair<FunctionSymbol, List<Var>>> signatures = ParsingUtil.extractFunDeclarations(pc,
					ctx.funDefs().funDefLHS(), true);
			Iterator<Pair<FunctionSymbol, List<Var>>> sigIt = signatures.iterator();
			HashMap<String, FunctionSymbol> m = new HashMap<>();
			for (String name : names) {
				m.put(name, sigIt.next().fst());
			}
			nestedFunctions.push(m);
			List<Term> funBodies = extractList(ctx.funDefs().term());
			Term letBody = extract(ctx.letFunBody);
			nestedFunctions.pop();
			sigIt = signatures.iterator();
			Set<NestedFunctionDef> defs = new HashSet<>();
			for (Term body : funBodies) {
				Pair<FunctionSymbol, List<Var>> p = sigIt.next();
				defs.add(NestedFunctionDef.make(p.fst(), p.snd(), body));
			}
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
