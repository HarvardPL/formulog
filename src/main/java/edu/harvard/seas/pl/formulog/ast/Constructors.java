package edu.harvard.seas.pl.formulog.ast;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

import org.pcollections.PMap;

import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager.TupleSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.RecordSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.util.FunctorUtil;
import edu.harvard.seas.pl.formulog.util.FunctorUtil.Memoizer;
import edu.harvard.seas.pl.formulog.util.TodoException;
import edu.harvard.seas.pl.formulog.util.Util;

public final class Constructors {

	private Constructors() {
		throw new AssertionError();
	}

	private static final Memoizer<Term> memo = new Memoizer<>();

	public static Term make(ConstructorSymbol sym, Term[] args) {
		assert sym.getArity() == args.length : sym + " " + Arrays.toString(args);
		if (sym instanceof BuiltInConstructorSymbol) {
			return lookupOrCreateBuiltInConstructor((BuiltInConstructorSymbol) sym, args);
		}
		if (sym instanceof ParameterizedConstructorSymbol) {
			return lookupOrCreateIndexedConstructor((ParameterizedConstructorSymbol) sym, args);
		}
		if (sym instanceof TupleSymbol) {
			return memo.lookupOrCreate(sym, args, () -> new Tuple((TupleSymbol) sym, args));
		}
		if (sym instanceof RecordSymbol) {
			return memo.lookupOrCreate(sym, args, () -> new Record((RecordSymbol) sym, args));
		}
		// if (sym instanceof SmtEqSymbol) {
		// return memo.lookupOrCreate(sym, args, () -> new SolverOperation(sym, args,
		// "="));
		// }
		switch (sym.getConstructorSymbolType()) {
		case SOLVER_UNINTERPRETED_FUNCTION:
			return memo.lookupOrCreate(sym, args, () -> new SolverUninterpretedFunction(sym, args));
		case SOLVER_VARIABLE:
			return memo.lookupOrCreate(sym, args, () -> new SolverVariable(sym, args));
		case SOLVER_CONSTRUCTOR_TESTER:
			return memo.lookupOrCreate(sym, args, () -> makeConstructorTester(sym, args));
		case SOLVER_CONSTRUCTOR_GETTER:
			return memo.lookupOrCreate(sym, args, () -> makeConstructorGetter(sym, args));
		case INDEX_CONSTRUCTOR:
		case VANILLA_CONSTRUCTOR:
			return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
		default:
			throw new IllegalArgumentException("Cannot create constructor for non-constructor symbol " + sym + ".");
		}
	}

	public static Term makeZeroAry(ConstructorSymbol sym) {
		return make(sym, Terms.emptyArray());
	}

	private static final Term trueTerm = makeZeroAry(BuiltInConstructorSymbol.TRUE);

	public static Term trueTerm() {
		return trueTerm;
	}

	private static final Term falseTerm = makeZeroAry(BuiltInConstructorSymbol.FALSE);

	public static Term falseTerm() {
		return falseTerm;
	}

	private static Term lookupOrCreateBuiltInConstructor(BuiltInConstructorSymbol sym, Term[] args) {
		Function<String, Term> makeSolverOp = op -> memo.lookupOrCreate(sym, args,
				() -> new SolverOperation(sym, args, op));
		switch (sym) {
		case FALSE:
			return makeSolverOp.apply("false");
		case TRUE:
			return makeSolverOp.apply("true");
		case NIL:
			return makeNil(sym, args);
		case CONS:
			return makeCons(sym, args);
		case CMP_EQ:
		case CMP_GT:
		case CMP_LT:
		case NONE:
		case SOME:
			return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
		case SMT_AND:
			return makeAnd(args);
		case SMT_IMP:
			return makeSolverOp.apply("=>");
		case SMT_ITE:
			return memo.lookupOrCreate(sym, args, () -> new SolverIte(sym, args));
		case SMT_NOT:
			return makeSolverOp.apply("not");
		case SMT_OR:
			return makeOr(args);
		case BV_ADD:
			return makeSolverOp.apply("bvadd");
		case BV_AND:
			return makeSolverOp.apply("bvand");
		case BV_MUL:
			return makeSolverOp.apply("bvmul");
		case BV_NEG:
			return makeSolverOp.apply("bvneg");
		case BV_OR:
			return makeSolverOp.apply("bvor");
		case BV_SDIV:
			return makeSolverOp.apply("bvsdiv");
		case BV_UDIV:
			return makeSolverOp.apply("bvudiv");
		case BV_SREM:
			return makeSolverOp.apply("bvsrem");
		case BV_UREM:
			return makeSolverOp.apply("bvurem");
		case BV_SUB:
			return makeSolverOp.apply("bvsub");
		case BV_XOR:
			return makeSolverOp.apply("bvxor");
		case FP_ADD:
			return makeSolverOp.apply("fp.add");
		case FP_DIV:
			return makeSolverOp.apply("fp.div");
		case FP_MUL:
			return makeSolverOp.apply("fp.mul");
		case FP_NEG:
			return makeSolverOp.apply("fp.neg");
		case FP_REM:
			return makeSolverOp.apply("fp.rem");
		case FP_SUB:
			return makeSolverOp.apply("fp.sub");
		case ARRAY_STORE:
			return makeSolverOp.apply("store");
		case ARRAY_CONST:
			return makeSolverOp.apply("const");
		case INT_ABS:
			return makeSolverOp.apply("abs");
		case INT_ADD:
			return makeSolverOp.apply("+");
		case INT_BIG_CONST:
		case INT_CONST:
			return makeIntConst(sym, args);
		case INT_DIV:
			return makeSolverOp.apply("div");
		case INT_GE:
			return makeSolverOp.apply(">=");
		case INT_GT:
			return makeSolverOp.apply(">");
		case INT_LE:
			return makeSolverOp.apply("<=");
		case INT_LT:
			return makeSolverOp.apply("<");
		case INT_MUL:
			return makeSolverOp.apply("*");
		case INT_NEG:
			return makeSolverOp.apply("-");
		case INT_MOD:
			return makeSolverOp.apply("mod");
		case INT_SUB:
			return makeSolverOp.apply("-");
		case STR_AT:
			return makeSolverOp.apply("str.at");
		case STR_CONCAT:
			return makeSolverOp.apply("str.++");
		case STR_CONTAINS:
			return makeSolverOp.apply("str.contains");
		case STR_INDEXOF:
			return makeSolverOp.apply("str.indexof");
		case STR_LEN:
			return makeSolverOp.apply("str.len");
		case STR_PREFIXOF:
			return makeSolverOp.apply("str.prefixof");
		case STR_REPLACE:
			return makeSolverOp.apply("str.replace");
		case STR_SUBSTR:
			return makeSolverOp.apply("str.substr");
		case STR_SUFFIXOF:
			return makeSolverOp.apply("str.suffixof");
		case ENTER_FORMULA:
			return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
		case EXIT_FORMULA:
			return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
		}
		throw new AssertionError("impossible");
	}

	private static Term makeAnd(Term[] args) {
		ConstructorSymbol sym = BuiltInConstructorSymbol.SMT_AND;
		return memo.lookupOrCreate(sym, args, () -> {
			// Term x = args[0];
			// Term y = args[1];
			// if (x instanceof Constructor) {
			// Constructor c = (Constructor) x;
			// if (c.equals(trueTerm)) {
			// return y;
			// } else if (c.equals(falseTerm)) {
			// return falseTerm;
			// }
			// }
			// if (y instanceof Constructor) {
			// Constructor c = (Constructor) y;
			// if (c.equals(trueTerm)) {
			// return x;
			// } else if (c.equals(falseTerm)) {
			// return falseTerm;
			// }
			// }
			return new SolverOperation(sym, args, "and");
		});
	}

	private static Term makeOr(Term[] args) {
		ConstructorSymbol sym = BuiltInConstructorSymbol.SMT_OR;
		return memo.lookupOrCreate(sym, args, () -> {
			// Term x = args[0];
			// Term y = args[1];
			// if (x instanceof Constructor) {
			// Constructor c = (Constructor) x;
			// if (c.equals(trueTerm)) {
			// return trueTerm;
			// } else if (c.equals(falseTerm)) {
			// return y;
			// }
			// }
			// if (y instanceof Constructor) {
			// Constructor c = (Constructor) y;
			// if (c.equals(trueTerm)) {
			// return trueTerm;
			// } else if (c.equals(falseTerm)) {
			// return x;
			// }
			// }
			return new SolverOperation(sym, args, "or");
		});
	}

	// Used for renaming variables to avoid capture.
	private static Map<PMap<SolverVariable, SmtLibTerm>, SolverVariable> binderMemo = new ConcurrentHashMap<>();

	private static SolverVariable renameBinder(SolverVariable x) {
		ConstructorSymbol newSym = new ConstructorSymbol() {

			@Override
			public int getArity() {
				return 0;
			}

			@Override
			public FunctorType getCompileTimeType() {
				// Only want return type of other variable, just in case it is a solver symbol
				// identified by a string argument.
				FunctorType funTy = x.getSymbol().getCompileTimeType();
				return new FunctorType(funTy.getRetType());
			}

			@Override
			public ConstructorSymbolType getConstructorSymbolType() {
				return ConstructorSymbolType.SOLVER_VARIABLE;
			}

		};
		SmtLibTerm y = (SmtLibTerm) make(newSym, Terms.emptyArray());
		return (SolverVariable) y;
	}

	private static class SolverLet extends AbstractConstructor {

		public static Term make(ConstructorSymbol sym, Term[] args) {
			return memo.lookupOrCreate(sym, args, () -> {
				// This causes too much of a slowdown
				// if (args[0] instanceof SolverVariable && args[2] instanceof SmtLibTerm
				// && meetsInliningThreshold(args[1])) {
				// PMap<SolverVariable, SmtLibTerm> subst =
				// HashTreePMap.singleton((SolverVariable) args[0],
				// (SmtLibTerm) args[1]);
				// return ((SmtLibTerm) args[2]).substSolverTerms(subst);
				// }
				return new SolverLet(sym, args);
			});
		}

		@SuppressWarnings("unused")
		private static boolean meetsInliningThreshold(Term t) {
			return t instanceof Primitive<?> || t instanceof SolverVariable;
		}

		private SolverLet(ConstructorSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			shim.print("(let ((");
			((SmtLibTerm) args[0]).toSmtLib(shim);
			shim.print(" ");
			((SmtLibTerm) args[1]).toSmtLib(shim);
			shim.print(")) ");
			((SmtLibTerm) args[2]).toSmtLib(shim);
			shim.print(")");
		}

		@Override
		public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
			// Rename bound variable to avoid variable capture.
			SolverVariable x = (SolverVariable) args[0];
			SolverVariable y = Util.lookupOrCreate(binderMemo, subst, () -> renameBinder(x));
			Term[] newArgs = new Term[args.length];
			newArgs[0] = y;
			newArgs[1] = ((SmtLibTerm) args[1]).substSolverTerms(subst);
			newArgs[2] = ((SmtLibTerm) args[2]).substSolverTerms(subst.plus(x, y));
			return (SmtLibTerm) copyWithNewArgs(newArgs);
		}

		@Override
		public String toString() {
			return "(#let " + args[0] + " = " + args[1] + " in " + args[2] + ")";
		}

		@Override
		public Set<SolverVariable> freeVars() {
			Set<SolverVariable> vars = new HashSet<>(((SmtLibTerm) args[2]).freeVars());
			vars.remove((SolverVariable) args[0]);
			vars.addAll(((SmtLibTerm) args[1]).freeVars());
			return vars;
		}

	}

	// private static class Quantifier extends AbstractConstructor {
	//
	// protected Quantifier(ConstructorSymbol sym, Term[] args) {
	// super(sym, args);
	// }
	//
	// @Override
	// public void toSmtLib(SmtLibShim shim) {
	// String quantifier = "forall (";
	// if (sym.equals(BuiltInConstructorSymbol.SMT_EXISTS)) {
	// quantifier = "exists (";
	// }
	// shim.print("(");
	// shim.print(quantifier);
	// for (Term t : getBoundVars()) {
	// SolverVariable x = (SolverVariable) t;
	// shim.print("(");
	// x.toSmtLib(shim);
	// shim.print(" ");
	// FunctorType ft = (FunctorType) x.getSymbol().getCompileTimeType();
	// shim.print(ft.getRetType());
	// shim.print(")");
	// }
	// shim.print(") ");
	// SmtLibTerm pattern = (SmtLibTerm) getPatternList();
	// // XXX Need to check if pattern is valid!
	// if (pattern != null) {
	// shim.print("(! ");
	// } else {
	// // Need to consume type annotation for none
	// shim.getTypeAnnotation((Constructor) args[2]);
	// }
	// ((SmtLibTerm) args[1]).toSmtLib(shim);
	// if (pattern != null) {
	// shim.print(" :pattern (");
	// for (Iterator<Term> it = breakPatternList(pattern).iterator(); it.hasNext();)
	// {
	// SmtLibTerm pat = (SmtLibTerm) it.next();
	// pat.toSmtLib(shim);
	// if (it.hasNext()) {
	// shim.print(" ");
	// }
	// }
	// shim.print("))");
	// }
	// shim.print(")");
	// }
	//
	// @Override
	// public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
	// // Rename bound variable to avoid variable capture.
	// List<SolverVariable> newVars = new ArrayList<>();
	// PMap<SolverVariable, SmtLibTerm> newSubst = subst;
	// for (Term t : getBoundVars()) {
	// SolverVariable x = (SolverVariable) t;
	// SolverVariable y = Util.lookupOrCreate(binderMemo, subst, () ->
	// renameBinder(x));
	// newVars.add(y);
	// newSubst = subst.plus(x, y);
	// }
	// Term[] newArgs = new Term[args.length];
	// newArgs[0] = makeFormulaVarList(newVars);
	// newArgs[1] = ((SmtLibTerm) args[1]).substSolverTerms(newSubst);
	// newArgs[2] = ((SmtLibTerm) args[2]).substSolverTerms(newSubst);
	// return (SmtLibTerm) copyWithNewArgs(newArgs);
	// }
	//
	// @Override
	// public String toString() {
	// String s = "(";
	// s += sym.equals(BuiltInConstructorSymbol.SMT_EXISTS) ? "exists " : "forall ";
	// for (Iterator<Term> it = getBoundVars().iterator(); it.hasNext();) {
	// s += it.next();
	// if (it.hasNext()) {
	// s += ", ";
	// }
	// }
	// Term pat = getPatternList();
	// if (pat != null) {
	// s += " : " + pat;
	// }
	// return s + ". " + args[1] + ")";
	// }
	//
	// private Term getPatternList() {
	// Constructor option = (Constructor) args[2];
	// if (option.getSymbol().equals(BuiltInConstructorSymbol.SOME)) {
	// return option.getArgs()[0];
	// }
	// return null;
	// }
	//
	// private static List<Term> breakList(Term list, ConstructorSymbol cons) {
	// List<Term> terms = new ArrayList<>();
	// Constructor xs = (Constructor) list;
	// while (xs.getSymbol().equals(cons)) {
	// terms.add(xs.getArgs()[0]);
	// xs = (Constructor) xs.getArgs()[1];
	// }
	// return terms;
	// }
	//
	// private static List<Term> breakPatternList(Term patternList) {
	// return breakList(patternList,
	// BuiltInConstructorSymbol.HETEROGENEOUS_LIST_CONS);
	// }
	//
	// private List<Term> getBoundVars() {
	// return breakList(args[0], BuiltInConstructorSymbol.SMT_VAR_LIST_CONS);
	// }
	//
	// private static Term makeFormulaVarList(List<SolverVariable> vars) {
	// Collections.reverse(vars);
	// Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.SMT_VAR_LIST_NIL);
	// for (SolverVariable x : vars) {
	// t = Constructors.make(BuiltInConstructorSymbol.SMT_VAR_LIST_CONS, new Term[]
	// { x, t });
	// }
	// return t;
	// }
	//
	// @Override
	// public Set<SolverVariable> freeVars() {
	// Set<SolverVariable> vars = super.freeVars();
	// vars.removeAll(getBoundVars());
	// return vars;
	// }
	//
	// }

	private static class Nil extends AbstractConstructor {

		protected Nil(ConstructorSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, shim);
		}

		@Override
		public String toString() {
			return "[]";
		}

	}

	private static class Cons extends AbstractConstructor {

		protected Cons(ConstructorSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, shim);
		}

		@Override
		public String toString() {
			List<Term> listArgs = new ArrayList<>();
			Term cur = this;
			while (cur instanceof Cons) {
				Cons cons = (Cons) cur;
				listArgs.add(cons.args[0]);
				cur = cons.args[1];
			}
			if (cur instanceof Nil) {
				String s = "[";
				for (Iterator<Term> it = listArgs.iterator(); it.hasNext();) {
					s += it.next();
					if (it.hasNext()) {
						s += ", ";
					}
				}
				return s + "]";
			} else {
				String s = "(";
				for (Term t : listArgs) {
					s += t;
					s += " :: ";
				}
				return s + cur + ")";
			}
		}

	}

	private static Term makeNil(ConstructorSymbol sym, Term[] args) {
		return memo.lookupOrCreate(sym, args, () -> new Nil(sym, args));
	}

	private static Term makeCons(ConstructorSymbol sym, Term[] args) {
		return memo.lookupOrCreate(sym, args, () -> new Cons(sym, args));
	}

	private static Term makeIntConst(ConstructorSymbol sym, Term[] args) {
		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {

			@Override
			public void toSmtLib(SmtLibShim shim) {
				shim.print(((Primitive<?>) args[0]).getVal().toString());
			}

		});
	}

	private static Term lookupOrCreateIndexedConstructor(ParameterizedConstructorSymbol sym, Term[] args) {
		Function<String, Term> makeSolverOp = op -> memo.lookupOrCreate(sym, args,
				() -> new SolverOperation(sym, args, op));
		BuiltInConstructorSymbolBase preSym = sym.getBase();
		switch (preSym) {
		case SMT_EQ:
			return makeSolverOp.apply("=");
		case SMT_LET:
			return SolverLet.make(sym, args);
		case ARRAY_DEFAULT:
			return makeSolverOp.apply("default");
		case ARRAY_SELECT:
			return makeSolverOp.apply("select");
		case BV_SGE:
			return makeSolverOp.apply("bvsge");
		case BV_SGT:
			return makeSolverOp.apply("bvsgt");
		case BV_SLE:
			return makeSolverOp.apply("bvsle");
		case BV_SLT:
			return makeSolverOp.apply("bvslt");
		case BV_UGE:
			return makeSolverOp.apply("bvuge");
		case BV_UGT:
			return makeSolverOp.apply("bvugt");
		case BV_ULE:
			return makeSolverOp.apply("bvule");
		case BV_ULT:
			return makeSolverOp.apply("bvult");
		case FP_EQ:
			return makeSolverOp.apply("fp.eq");
		case FP_GE:
			return makeSolverOp.apply("fp.geq");
		case FP_GT:
			return makeSolverOp.apply("fp.gt");
		case FP_IS_NAN:
			return makeSolverOp.apply("fp.isNaN");
		case FP_LE:
			return makeSolverOp.apply("fp.leq");
		case FP_LT:
			return makeSolverOp.apply("fp.lt");
		case SMT_EXISTS:
		case SMT_FORALL:
		case SMT_EXISTS_PAT:
		case SMT_FORALL_PAT:
			throw new TodoException();
//			return memo.lookupOrCreate(sym, args, () -> new Quantifier(sym, args));
//			
//			return memo.lookupOrCreate(sym, args, () -> new Quantifier(sym, args));
//			return memo.lookupOrCreate(sym, args, () -> new Quantifier(sym, args));
//			return memo.lookupOrCreate(sym, args, () -> new Quantifier(sym, args));
		case BV_TO_BV_SIGNED:
			return makeBvToBvSigned(sym, args);
		case BV_TO_BV_UNSIGNED:
			return makeBvToBvUnsigned(sym, args);
		case FP_TO_FP:
			return makeFpToFp(sym, args);
		case BV_TO_FP:
			return makeBvToFp(sym, args);
		case FP_TO_BV:
			return makeFpToBv(sym, args);
		case BV_CONST:
			return makeBVConst(sym, args);
		case BV_BIG_CONST:
			return makeBVBigConst(sym, args);
		case FP_BIG_CONST:
		case FP_CONST:
			return makeConstant(sym, args);
		}
		throw new AssertionError("impossible");
	}

	private static int coerceNatIndex(Param param) {
		return ((TypeIndex) param.getType()).getIndex();
	}
	
	private static Term makeBVConst(ParameterizedConstructorSymbol psym, Term[] args) {
		return memo.lookupOrCreate(psym, args, () -> new AbstractConstructor(psym, args) {

			@Override
			public void toSmtLib(SmtLibShim shim) {
				I32 arg = (I32) args[0];
				int width = coerceNatIndex(psym.getArgs().get(0));
				String s = Integer.toBinaryString(arg.getVal());
				int len = s.length();
				if (width > len) {
					String pad = "";
					for (int w = len; w < width; w++) {
						pad += "0";
					}
					s = pad + s;
				} else if (width < len) {
					s = s.substring(len - width, len);
				}
				shim.print("#b" + s);
			}

		});
	}

	private static Term makeBVBigConst(ParameterizedConstructorSymbol psym, Term[] args) {
		return memo.lookupOrCreate(psym, args, () -> new AbstractConstructor(psym, args) {

			@Override
			public void toSmtLib(SmtLibShim shim) {
				I64 arg = (I64) args[0];
				int width = coerceNatIndex(psym.getArgs().get(0));
				String s = Long.toBinaryString(arg.getVal());
				int len = s.length();
				if (width > len) {
					String pad = "";
					for (int w = len; w < width; w++) {
						pad += "0";
					}
					s = pad + s;
				} else if (width < len) {
					s = s.substring(len - width, len);
				}
				shim.print("#b" + s);
			}

		});
	}

	private static Term makeConstant(ConstructorSymbol sym, Term[] args) {
		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {

			@Override
			public void toSmtLib(SmtLibShim shim) {
				((SmtLibTerm) args[0]).toSmtLib(shim);
			}

		});
	}

	private static int idx(Term[] args, int i) {
		Constructor t = (Constructor) args[i];
		return ((I32) t.getArgs()[0]).getVal();
	}

	private static Term makeBvToBvSigned(ParameterizedConstructorSymbol sym, Term[] args) {
		throw new TodoException();
//		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {
//
//			@Override
//			public void toSmtLib(SmtLibShim shim) {
//				int idx1 = idx(args, 1);
//				int idx2 = idx(args, 2);
//				SmtLibTerm t = (SmtLibTerm) args[0];
//				if (idx1 < idx2) {
//					shim.print("(");
//					shim.print("(_ sign_extend " + (idx2 - idx1) + ") ");
//					t.toSmtLib(shim);
//					shim.print(")");
//				} else if (idx1 == idx2) {
//					t.toSmtLib(shim);
//				} else {
//					shim.print("(");
//					shim.print("(_ extract " + (idx2 - 1) + " 0) ");
//					t.toSmtLib(shim);
//					shim.print(")");
//				}
//			}
//
//		});
	}

	private static Term makeBvToBvUnsigned(ParameterizedConstructorSymbol sym, Term[] args) {
		throw new TodoException();
//		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {
//
//			@Override
//			public void toSmtLib(SmtLibShim shim) {
//				int idx1 = idx(args, 1);
//				int idx2 = idx(args, 2);
//				SmtLibTerm t = (SmtLibTerm) args[0];
//				if (idx1 < idx2) {
//					shim.print("(");
//					shim.print("(_ zero_extend " + (idx2 - idx1) + ") ");
//					t.toSmtLib(shim);
//					shim.print(")");
//				} else if (idx1 == idx2) {
//					t.toSmtLib(shim);
//				} else {
//					shim.print("(");
//					shim.print("(_ extract " + (idx2 - 1) + " 0) ");
//					t.toSmtLib(shim);
//					shim.print(")");
//				}
//			}
//
//		});

	}

	private static Term makeBvToFp(ParameterizedConstructorSymbol sym, Term[] args) {
		throw new TodoException();
//		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {
//
//			@Override
//			public void toSmtLib(SmtLibShim shim) {
//				int exponent = idx(args, 2);
//				int significand = idx(args, 3);
//				shim.print("((_ to_fp " + exponent + " " + significand + ") RNE ");
//				((SmtLibTerm) args[0]).toSmtLib(shim);
//				shim.print(")");
//			}
//
//		});
	}

	private static Term makeFpToFp(ParameterizedConstructorSymbol sym, Term[] args) {
		throw new TodoException();
//		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {
//
//			@Override
//			public void toSmtLib(SmtLibShim shim) {
//				int exponent = idx(args, 3);
//				int significand = idx(args, 4);
//				shim.print("((_ to_fp " + exponent + " " + significand + ") RNE ");
//				((SmtLibTerm) args[0]).toSmtLib(shim);
//				shim.print(")");
//			}
//
//		});
	}

	private static Term makeFpToBv(ParameterizedConstructorSymbol sym, Term[] args) {
		throw new TodoException();
//		return memo.lookupOrCreate(sym, args, () -> new AbstractConstructor(sym, args) {
//
//			@Override
//			public void toSmtLib(SmtLibShim shim) {
//				int width = idx(args, 3);
//				shim.print("((_ fp.to_sbv " + width + ") RNE ");
//				((SmtLibTerm) args[0]).toSmtLib(shim);
//				shim.print(")");
//			}
//
//		});
	}

	private static abstract class AbstractConstructor extends AbstractTerm implements Constructor {

		protected final ConstructorSymbol sym;
		protected final Term[] args;
		protected final boolean isGround;
		protected final boolean containsFunctionCall;

		protected AbstractConstructor(ConstructorSymbol sym, Term[] args) {
			assert noneNull(args) : sym;
			this.sym = sym;
			this.args = args;
			boolean g = true;
			boolean f = false;
			for (Term t : args) {
				g &= t.isGround();
				f |= t.containsUnevaluatedTerm();
			}
			isGround = g;
			containsFunctionCall = f;
		}

		private boolean noneNull(Term[] ts) {
			for (Term t : ts) {
				if (t == null) {
					return false;
				}
			}
			return true;
		}

		@Override
		public boolean isGround() {
			return isGround;
		}

		@Override
		public boolean containsUnevaluatedTerm() {
			return containsFunctionCall;
		}

		@Override
		public ConstructorSymbol getSymbol() {
			return sym;
		}

		@Override
		public Term[] getArgs() {
			return args;
		}

		@Override
		public String toString() {
			return FunctorUtil.toString(sym, args);
		}

		@Override
		public Term copyWithNewArgs(Term[] args) {
			return make(sym, args);
		}

		@Override
		public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
			if (subst.containsKey(this)) {
				return subst.get(this);
			}
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = ((SmtLibTerm) args[i]).substSolverTerms(subst);
			}
			return (SmtLibTerm) copyWithNewArgs(newArgs);
		}

		@Override
		public Set<SolverVariable> freeVars() {
			Set<SolverVariable> vars = new HashSet<>();
			for (Term t : args) {
				vars.addAll(((SmtLibTerm) t).freeVars());
			}
			return vars;
		}

	}

	public static class VanillaConstructor extends AbstractConstructor {

		private VanillaConstructor(ConstructorSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, shim);
		}

	}

	public static class Tuple extends AbstractConstructor {

		private Tuple(TupleSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, shim);
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder("(");
			for (int i = 0; i < args.length; ++i) {
				sb.append(args[i]);
				if (i < args.length - 1) {
					sb.append(", ");
				}
			}
			sb.append(")");
			return sb.toString();
		}

	}

	public static class Record extends AbstractConstructor {

		private Record(RecordSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, shim);
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder("{ ");
			int i = 0;
			for (FunctionSymbol label : ((RecordSymbol) sym).getLabels()) {
				sb.append(label);
				sb.append("=");
				sb.append(args[i]);
				sb.append("; ");
				++i;
			}
			sb.append("}");
			return sb.toString();
		}

	}

	public static class SolverVariable extends AbstractConstructor {

		private static final AtomicInteger cnt = new AtomicInteger();
		private static final Map<SolverVariable, Integer> varIds = new ConcurrentHashMap<>();

		public SolverVariable(ConstructorSymbol sym, Term[] args) {
			super(sym, args);
			varIds.putIfAbsent(this, cnt.getAndIncrement());
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			shim.print(this);
		}

		@Override
		public String toString() {
			Type ty = ((FunctorType) sym.getCompileTimeType()).getRetType();
			ty = ((AlgebraicDataType) ty).getTypeArgs().get(0);
			return "#{" + args[0] + "}[" + ty + "]";
			// return "#x" + varIds.get(this) + "[" + ty + "]";
		}

		@Override
		public Set<SolverVariable> freeVars() {
			return Collections.singleton(this);
		}

	}

	private static Constructor makeConstructorTester(ConstructorSymbol sym, Term[] args) {
		assert sym.toString().matches("#is_.*");
		String s = "|is-" + sym.toString().substring(4) + "|";
		return new AbstractConstructor(sym, args) {

			@Override
			public void toSmtLib(SmtLibShim shim) {
				shim.print("(");
				shim.print(s);
				shim.print(" ");
				((SmtLibTerm) args[0]).toSmtLib(shim);
				shim.print(")");
			}

		};
	}

	private static Constructor makeConstructorGetter(ConstructorSymbol sym, Term[] args) {
		String s = "|" + sym.toString() + "|";
		return new AbstractConstructor(sym, args) {

			@Override
			public void toSmtLib(SmtLibShim shim) {
				shim.print("(");
				shim.print(s);
				shim.print(" ");
				((SmtLibTerm) args[0]).toSmtLib(shim);
				shim.print(")");
			}

		};
	}

	public static class SolverUninterpretedFunction extends AbstractConstructor {

		protected SolverUninterpretedFunction(ConstructorSymbol sym, Term[] args) {
			super(sym, args);
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, shim);
		}

	}

	public static class SolverOperation extends AbstractConstructor {

		private final String op;

		protected SolverOperation(ConstructorSymbol sym, Term[] args, String op) {
			super(sym, args);
			this.op = op;
		}

		@Override
		public void toSmtLib(SmtLibShim shim) {
			Constructors.toSmtLib(this, op, shim);
		}

		private String getSyntax() {
			if (sym instanceof ParameterizedConstructorSymbol) {
				if (((ParameterizedConstructorSymbol) sym).getBase()
						.equals(BuiltInConstructorSymbolBase.SMT_EQ)) {
					return "#=";
				}
			}
			if (sym instanceof BuiltInConstructorSymbol) {
				switch ((BuiltInConstructorSymbol) sym) {
				case SMT_AND:
					return "/\\";
				case SMT_IMP:
					return "==>";
				case SMT_NOT:
					return "~";
				case SMT_OR:
					return "\\/";
				default:
					return null;
				}
			}
			return null;
		}

		@Override
		public String toString() {
			String syntax = getSyntax();
			if (syntax == null) {
				return super.toString();
			}
			if (args.length == 1) {
				return "(" + syntax + " " + args[0] + ")";
			}
			if (args.length == 2) {
				return "(" + args[0] + " " + syntax + " " + args[1] + ")";
			}
			throw new AssertionError("impossible");
		}

	}

	private static class SolverIte extends SolverOperation {

		protected SolverIte(ConstructorSymbol sym, Term[] args) {
			super(sym, args, "ite");
		}

		@Override
		public String toString() {
			return "(#if " + args[0] + " then " + args[1] + " else " + args[2] + ")";
		}

	}

	private static void toSmtLib(Constructor c, String repr, SmtLibShim shim) {
		ConstructorSymbol sym = c.getSymbol();
		if (sym.getArity() > 0) {
			shim.print("(");
		}
		String typeAnnotation = shim.getTypeAnnotation(c);
		if (typeAnnotation != null) {
			shim.print("(as ");
			shim.print(repr);
			shim.print(" ");
			shim.print(typeAnnotation);
			shim.print(")");
		} else {
			shim.print(repr);
		}
		for (Term t : c.getArgs()) {
			SmtLibTerm tt = (SmtLibTerm) t;
			shim.print(" ");
			tt.toSmtLib(shim);
		}
		if (sym.getArity() > 0) {
			shim.print(")");
		}
	}

	private static void toSmtLib(Constructor c, SmtLibShim shim) {
		toSmtLib(c, c.getSymbol().toString(), shim);
	}

}
