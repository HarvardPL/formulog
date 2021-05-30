package edu.harvard.seas.pl.formulog.ast;

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

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.FunctorUtil;
import edu.harvard.seas.pl.formulog.util.FunctorUtil.Memoizer;
import edu.harvard.seas.pl.formulog.util.Util;

public final class FunctionCallFactory {

	private final FunctionDefManager defManager;
	private final Memoizer<FunctionCall> memo = new Memoizer<>();

	private static final AtomicInteger cnt = new AtomicInteger();
	private static final boolean debug = System.getProperty("callTrace") != null;
	private static final int memoizeThreshold = Configuration.memoizeThreshold();

	private final Map<Symbol, Map<List<Term>, Term>> callMemo = new ConcurrentHashMap<>();

	public FunctionCallFactory(FunctionDefManager defManager) {
		this.defManager = defManager;
		for (BuiltInFunctionSymbol sym : BuiltInFunctionSymbol.values()) {
			switch (sym) {
			case PRINT:
			case HEAVY_HITTER:
				purityCheckCache.put(sym, true);
				break;
			default:
				purityCheckCache.put(sym, false);
			}
		}
	}

	public FunctionCall make(FunctionSymbol sym, Term[] args) {
		if (sym.getArity() != args.length) {
			throw new IllegalArgumentException("Symbol " + sym + " has arity " + sym.getArity() + " but args "
					+ Arrays.toString(args) + " have length " + args.length);
		}
		return memo.lookupOrCreate(sym, args, () -> new FunctionCall(sym, args));
	}

	public FunctionDefManager getDefManager() {
		return defManager;
	}

	public void clearMemoCache() {
		callMemo.clear();
	}

	private final Map<FunctionSymbol, Boolean> purityCheckCache = new ConcurrentHashMap<>();

	private final TermVisitor<Void, Boolean> termSideEffectVisitor = new TermVisitor<Void, Boolean>() {

		@Override
		public Boolean visit(Var t, Void in) {
			return false;
		}

		@Override
		public Boolean visit(Constructor c, Void in) {
			boolean hasSideEffect = false;
			for (Term arg : c.getArgs()) {
				hasSideEffect |= arg.accept(this, in);
			}
			return hasSideEffect;
		}

		@Override
		public Boolean visit(Primitive<?> p, Void in) {
			return false;
		}

		@Override
		public Boolean visit(Expr e, Void in) {
			return e.accept(exprSideEffectVisitor, in);
		}

	};

	private final ExprVisitor<Void, Boolean> exprSideEffectVisitor = new ExprVisitor<Void, Boolean>() {

		@Override
		public Boolean visit(MatchExpr matchExpr, Void in) {
			if (matchExpr.getMatchee().accept(termSideEffectVisitor, in)) {
				return true;
			}
			for (MatchClause cl : matchExpr) {
				if (cl.getRhs().accept(termSideEffectVisitor, in)) {
					return true;
				}
			}
			return false;
		}

		@Override
		public Boolean visit(FunctionCall funcCall, Void in) {
			if (hasSideEffects(funcCall.getSymbol())) {
				return true;
			}
			boolean hasSideEffects = false;
			for (Term arg : funcCall.getArgs()) {
				hasSideEffects |= arg.accept(termSideEffectVisitor, in);
			}
			return hasSideEffects;
		}

		@Override
		public Boolean visit(LetFunExpr funcDefs, Void in) {
			throw new AssertionError("impossible - lef fun expressions do not exist at runtime");
		}

		@Override
		public Boolean visit(Fold fold, Void in) {
			if (hasSideEffects(fold.getFunction())) {
				return true;
			}
			for (Term arg : fold.getArgs()) {
				if (arg.accept(termSideEffectVisitor, in)) {
					return true;
				}
			}
			return false;
		}

	};

	private boolean hasSideEffects(FunctionSymbol sym) {
		Boolean hasSideEffect = purityCheckCache.get(sym);
		if (hasSideEffect == null) {
			if (Configuration.doSideEffectAnalysis) {
				hasSideEffect = doSideEffectAnalysis(sym);
			} else {
				hasSideEffect = false;
			}
			purityCheckCache.put(sym, hasSideEffect);
		}
		return hasSideEffect;
	}

	private boolean doSideEffectAnalysis(FunctionSymbol sym) {
		FunctionDef def = defManager.lookup(sym);
		if (def instanceof UserFunctionDef) {
			// Put in a placeholder to make sure the analysis does not loop indefinitely.
			purityCheckCache.putIfAbsent(sym, false);
			Boolean res = ((UserFunctionDef) def).getBody().accept(termSideEffectVisitor, null);
			assert res != null;
			return res;
		}
		return false;
	}

	public class FunctionCall extends AbstractTerm implements Functor<FunctionSymbol>, Expr {

		private final FunctionSymbol sym;
		private final Term[] args;
		private final boolean isGround;

		private FunctionCall(FunctionSymbol sym, Term[] args) {
			this.sym = sym;
			this.args = args;
			boolean b = true;
			for (Term t : args) {
				b &= t.isGround();
			}
			isGround = b;
		}

		@Override
		public FunctionSymbol getSymbol() {
			return sym;
		}

		@Override
		public Term[] getArgs() {
			return args;
		}

		@Override
		public FunctionCall copyWithNewArgs(Term[] newArgs) {
			return make(sym, newArgs);
		}

		@Override
		public boolean containsUnevaluatedTerm() {
			return true;
		}

		@Override
		public Term applySubstitution(Substitution s) {
			if (isGround) {
				return this;
			}
			Term[] args = getArgs();
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].applySubstitution(s);
			}
			return make(sym, newArgs);
		}

		@Override
		public boolean isGround() {
			return isGround;
		}

		@Override
		public String toString() {
			return FunctorUtil.toString(sym, args);
		}

		@Override
		public Term normalize(Substitution s) throws EvaluationException {
			Integer id = null;
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].normalize(s);
			}
			if (debug) {
				id = cnt.getAndIncrement();
				String msg = "BEGIN CALL #" + id + "\n";
				msg += "Function: " + sym + "\n";
				msg += "Arguments: " + Arrays.toString(newArgs) + "\n";
				msg += "***\n";
				System.err.println(msg);
			}
			Term r;
			try {
				if (memoizeThreshold > -1 && !hasSideEffects(sym)) {
					r = computeWithMemoization(newArgs);
				} else {
					r = computeWithoutMemoization(newArgs);
				}
			} catch (Throwable e) {
				throw new EvaluationException(e);
			}
			if (debug) {
				String msg = "END CALL #" + id + "\n";
				msg += "Function: " + sym + "\n";
				msg += "Arguments: " + Arrays.toString(newArgs) + "\n";
				msg += "Result: " + r + "\n";
				msg += "***\n";
				System.err.println(msg);
			}
			return r;
		}

		private Term computeWithMemoization(Term[] newArgs) throws EvaluationException {
			Map<List<Term>, Term> m = Util.lookupOrCreate(callMemo, sym, () -> new ConcurrentHashMap<>());
			List<Term> key = Arrays.asList(newArgs);
			Term r = m.get(key);
			if (r == null) {
				long start = System.nanoTime();
				r = defManager.lookup(sym).evaluate(newArgs);
				long time = (System.nanoTime() - start) / 1000000;
				if (Configuration.recordFuncDiagnostics) {
					Configuration.recordFuncTime(sym, time);
				}
				if (time >= memoizeThreshold) {
					m.put(key, r);
				}
			}
			return r;
		}

		private Term computeWithoutMemoization(Term[] newArgs) throws EvaluationException {
			long start = 0;
			if (Configuration.recordFuncDiagnostics) {
				start = System.nanoTime();
			}
			Term r = defManager.lookup(sym).evaluate(newArgs);
			if (Configuration.recordFuncDiagnostics) {
				long time = (System.nanoTime() - start) / 1000000;
				Configuration.recordFuncTime(sym, time);
			}
			return r;
		}

		public FunctionCallFactory getFactory() {
			return FunctionCallFactory.this;
		}

		@Override
		public <I, O> O accept(ExprVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public <I, O, E extends Throwable> O accept(ExprVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

	}

}
