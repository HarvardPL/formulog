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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInPredicateSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.EmptySubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Util;

public final class Atoms {

	private Atoms() {
		throw new AssertionError();
	}

	public static interface Atom {

		Symbol getSymbol();

		Term[] getArgs();

		boolean isNegated();

		<I, O> O visit(AtomVisitor<I, O> visitor, I in);

		<I, O, E extends Throwable> O visit(AtomVisitorExn<I, O, E> visitor, I in) throws E;

	}

	public static interface AtomVisitor<I, O> {

		O visit(NormalAtom normalAtom, I in);

		O visit(UnifyAtom unifyAtom, I in);

	}

	public static interface AtomVisitorExn<I, O, E extends Throwable> {

		O visit(NormalAtom normalAtom, I in) throws E;

		O visit(UnifyAtom unifyAtom, I in) throws E;

	}

	private static final Map<Object, Object> memoPos = new ConcurrentHashMap<>();
	private static final Map<Object, Object> memoNeg = new ConcurrentHashMap<>();

	@SuppressWarnings("unchecked")
	public static Atom get(Symbol sym, Term[] args, boolean neg) {
		if (!sym.getSymbolType().isRelationType()) {
			throw new IllegalArgumentException("Non-relation symbol: " + sym);
		}
		if (sym.getArity() != args.length) {
			throw new IllegalArgumentException("Symbol " + sym + " has arity " + sym.getArity() + " but args "
					+ Arrays.toString(args) + " have length " + args.length);
		}

		Map<Object, Object> m = neg ? memoNeg : memoPos;
		Object k = sym;
		for (int i = 0; i < args.length; ++i) {
			m = (Map<Object, Object>) Util.lookupOrCreate(m, k, () -> new ConcurrentHashMap<>());
			k = args[i];
		}
		Object o = m.get(k);
		if (o != null) {
			return (Atom) o;
		}

		Atom a;
		if (sym instanceof BuiltInPredicateSymbol) {
			switch ((BuiltInPredicateSymbol) sym) {
			case UNIFY:
				a = new UnifyAtom(args, neg);
				break;
			default:
				throw new AssertionError();
			}
		} else {
			a = new NormalAtom(sym, args.length == 0 ? Terms.emptyArray() : args, neg);
		}
		return (Atom) Util.lookupOrCreate(m, k, () -> a);
	}

	public static Atom getPositive(Symbol sym, Term[] args) {
		return get(sym, args, false);
	}

	public static Atom getNegated(Symbol sym, Term[] args) {
		return get(sym, args, true);
	}

	public static class NormalAtom implements Atom {

		private final Symbol sym;
		private final Term[] args;
		private final boolean neg;

		protected NormalAtom(Symbol sym, Term[] args, boolean neg) {
			this.sym = sym;
			this.args = args;
			this.neg = neg;
		}

		@Override
		public Symbol getSymbol() {
			return sym;
		}

		@Override
		public Term[] getArgs() {
			return args;
		}

		@Override
		public boolean isNegated() {
			return neg;
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			if (neg) {
				sb.append("!");
			}
			sb.append(sym.toString());
			int arity = sym.getArity();
			if (arity > 0) {
				sb.append('(');
				for (int i = 0; i < arity; ++i) {
					sb.append(args[i]);
					if (i < arity - 1) {
						sb.append(", ");
					}
				}
				sb.append(')');
			}
			return sb.toString();
		}

		@Override
		public <I, O> O visit(AtomVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public <I, O, E extends Throwable> O visit(AtomVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

	}

	public static class UnifyAtom implements Atom {

		private final Term[] args;
		private final boolean neg;

		private UnifyAtom(Term[] args, boolean neg) {
			assert args.length == 2;
			this.args = args;
			this.neg = neg;
		}

		@Override
		public Symbol getSymbol() {
			return BuiltInPredicateSymbol.UNIFY;
		}

		@Override
		public Term[] getArgs() {
			return args;
		}

		@Override
		public boolean isNegated() {
			return neg;
		}

		@Override
		public <I, O> O visit(AtomVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			String s = neg ? " != " : " = ";
			return args[0] + s + args[1];
		}

		@Override
		public <I, O, E extends Throwable> O visit(AtomVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

	}

	public static Set<Var> varSet(Atom a) {
		Set<Var> vars = new HashSet<>();
		for (Term t : a.getArgs()) {
			vars.addAll(Terms.varSet(t));
		}
		return vars;
	}

	public static Atom applySubstitution(Atom a, Substitution s) {
		Term[] args = a.getArgs();
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].applySubstitution(s);
		}
		return Atoms.get(a.getSymbol(), newArgs, a.isNegated());
	}

	public static Atom normalize(Atom a, Substitution s) throws EvaluationException {
		Term[] args = a.getArgs();
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].reduce(EmptySubstitution.INSTANCE);
		}
		return Atoms.get(a.getSymbol(), newArgs, a.isNegated());
	}
	
	public static Atom normalize(Atom a) throws EvaluationException {
		return normalize(a, EmptySubstitution.INSTANCE);
	}
	
}
