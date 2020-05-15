package formulog.ast;

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



import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import formulog.Configuration;
import formulog.ast.Exprs.ExprVisitor;
import formulog.ast.Exprs.ExprVisitorExn;
import formulog.eval.EvaluationException;
import formulog.functions.FunctionDefManager;
import formulog.symbols.BuiltInFunctionSymbol;
import formulog.symbols.FunctionSymbol;
import formulog.symbols.Symbol;
import formulog.unification.Substitution;
import formulog.util.FunctorUtil;
import formulog.util.Util;
import formulog.util.FunctorUtil.Memoizer;

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
			if (memoizeThreshold > -1 && !hasSideEffects()) {
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
		
		private boolean hasSideEffects() {
			// XXX This is rough, since it doesn't take into account the call
			// graph (i.e., A could call B which is side effecting, but this
			// would say that A is not).
			return sym.equals(BuiltInFunctionSymbol.PRINT);
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
