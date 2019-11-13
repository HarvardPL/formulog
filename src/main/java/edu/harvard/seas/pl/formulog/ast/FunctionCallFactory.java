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

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
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
		public boolean containsFunctionCall() {
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
			if (memoizeThreshold > -1) {
				r = computeWithMemoization(newArgs);
			} else {
				r = computeWithoutMemoization(newArgs);
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
