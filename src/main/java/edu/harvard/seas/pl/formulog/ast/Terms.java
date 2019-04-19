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

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.ExceptionalFunction;

public final class Terms {

	private Terms() {
		throw new AssertionError();
	}

	private static final Term[] EMPTY_TERMS_ARR = new Term[0];
	
	public static Term[] emptyArray() {
		return EMPTY_TERMS_ARR;
	}
	
	public static Term[] singletonArray(Term t) {
		return new Term[] { t };
	}
	
	public static Term[] map(Term[] ts, Function<Term, Term> f) {
		Term[] ys = new Term[ts.length];
		for (int i = 0; i < ts.length; ++i) {
			ys[i] = f.apply(ts[i]);
		}
		return ys;
	}
	
	public static <E extends Exception> Term[] mapExn(Term[] ts, ExceptionalFunction<Term, Term, E> f) throws E {
		Term[] ys = new Term[ts.length];
		for (int i = 0; i < ts.length; ++i) {
			ys[i] = f.apply(ts[i]);
		}
		return ys;
	}

	public static Set<Var> varSet(Term t) {
		return t.visit(new TermVisitor<Set<Var>, Set<Var>>() {

			@Override
			public Set<Var> visit(Var t, Set<Var> in) {
				in.add(t);
				return in;
			}

			@Override
			public Set<Var> visit(Constructor t, Set<Var> in) {
				for (Term tt : t.getArgs()) {
					tt.visit(this, in);
				}
				return in;
			}

			@Override
			public Set<Var> visit(Primitive<?> prim, Set<Var> in) {
				return in;
			}

			@Override
			public Set<Var> visit(FunctionCall t, Set<Var> in) {
				for (Term tt : t.getArgs()) {
					tt.visit(this, in);
				}
				return in;
			}

		}, new HashSet<>());
	}

	public static boolean isGround(Term t, Set<Var> boundVars) {
		return boundVars.containsAll(varSet(t));
	}
	
	public static Set<Var> getNonBindingVarInstances(Term t) {
		Set<Var> vars = new HashSet<>();
		t.visit(new TermVisitor<Void, Void>() {

			@Override
			public Void visit(Var t, Void in) {
				return null;
			}

			@Override
			public Void visit(Constructor t, Void in) {
				for (Term arg : t.getArgs()) {
					arg.visit(this, in);
				}
				return null;
			}

			@Override
			public Void visit(Primitive<?> prim, Void in) {
				return null;
			}

			@Override
			public Void visit(FunctionCall function, Void in) {
				vars.addAll(Terms.varSet(function));
				return null;
			}
			
		}, null);
		return vars;
	}
	
	public static Set<Var> getBindingVarInstances(Term t) {
		Set<Var> vars = new HashSet<>();
		t.visit(new TermVisitor<Void, Void>() {

			@Override
			public Void visit(Var t, Void in) {
				vars.add(t);
				return null;
			}

			@Override
			public Void visit(Constructor t, Void in) {
				for (Term arg : t.getArgs()) {
					arg.visit(this, in);
				}
				return null;
			}

			@Override
			public Void visit(Primitive<?> prim, Void in) {
				return null;
			}

			@Override
			public Void visit(FunctionCall function, Void in) {
				return null;
			}
			
		}, null);
		return vars;
	}

	public static interface TermVisitor<I, O> {

		O visit(Var t, I in);

		O visit(Constructor c, I in);

		O visit(Primitive<?> p, I in);

		O visit(FunctionCall f, I in);

	}

	public static interface TermVisitorExn<I, O, E extends Throwable> {

		O visit(Var x, I in) throws E;

		O visit(Constructor c, I in) throws E;

		O visit(Primitive<?> p, I in) throws E;

		O visit(FunctionCall f, I in) throws E;

	}

	public static Term lookup(Term t, Substitution subst) {
		if (t instanceof Var) {
			Var v = (Var) t;
			if (subst.containsKey(v)) {
				return subst.get(v);
			}
		}
		return t;
	}

}
