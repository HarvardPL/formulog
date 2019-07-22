package edu.harvard.seas.pl.formulog.ast;

import java.util.Comparator;

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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
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
	
	public static Term[] normalize(Term[] ts, Substitution s) throws EvaluationException {
		Term[] newTs = new Term[ts.length];
		for (int i = 0; i < ts.length; ++i) {
			newTs[i] = ts[i].normalize(s);
		}
		return newTs;
	}

//	private static final ExprVisitor<Set<Var>, Void> exprVarExtractor = new ExprVisitor<Set<Var>, Void>() {
//
//		@Override
//		public Void visit(MatchExpr matchExpr, Set<Var> in) {
//			varSetOfTerm(matchExpr.getMatchee(), in);
//			for (MatchClause cl : matchExpr.getClauses()) {
//				Set<Var> patternVars = varSet(cl.getLhs());
//				Set<Var> rhsVars = varSet(cl.getRhs());
//				rhsVars.removeAll(patternVars);
//				in.addAll(rhsVars);
//			}
//			return null;
//		}
//
//		@Override
//		public Void visit(FunctionCall funcCall, Set<Var> in) {
//			for (Term arg : funcCall.getArgs()) {
//				varSetOfTerm(arg, in);
//			}
//			return null;
//		}
//
//	};
//
//	private static final TermVisitor<Set<Var>, Void> termVarExtractor = new TermVisitor<Set<Var>, Void>() {
//
//		@Override
//		public Void visit(Var t, Set<Var> in) {
//			in.add(t);
//			return null;
//		}
//
//		@Override
//		public Void visit(Constructor c, Set<Var> in) {
//			for (Term arg : c.getArgs()) {
//				varSetOfTerm(arg, in);
//			}
//			return null;
//		}
//
//		@Override
//		public Void visit(Primitive<?> p, Set<Var> in) {
//			return null;
//		}
//
//		@Override
//		public Void visit(Expr e, Set<Var> in) {
//			varSetOfExpr(e, in);
//			return null;
//		}
//
//	};

//	private static void varSetOfExpr(Expr e, Set<Var> vars) {
//		if (!e.isGround()) {
//			e.visit(exprVarExtractor, vars);
//		}
//	}
//
//	private static void varSetOfTerm(Term t, Set<Var> vars) {
//		if (!t.isGround()) {
//			t.visit(termVarExtractor, vars);
//		}
//	}
//
//	public static Set<Var> varSet(Term t) {
//		Set<Var> vars = new HashSet<>();
//		varSetOfTerm(t, vars);
//		return vars;
//	}

	public static boolean isGround(Term t, Set<Var> boundVars) {
		return boundVars.containsAll(t.varSet());
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
			public Void visit(Expr expr, Void in) {
				vars.addAll(expr.varSet());
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
			public Void visit(Expr expr, Void in) {
				return null;
			}

		}, null);
		return vars;
	}

	public static interface TermVisitor<I, O> {

		O visit(Var t, I in);

		O visit(Constructor c, I in);

		O visit(Primitive<?> p, I in);

		O visit(Expr e, I in);

	}

	public static interface TermVisitorExn<I, O, E extends Throwable> {

		O visit(Var x, I in) throws E;

		O visit(Constructor c, I in) throws E;

		O visit(Primitive<?> p, I in) throws E;

		O visit(Expr e, I in) throws E;

	}
	
	public static final Term minTerm = new Term() {

		@Override
		public <I, O> O visit(TermVisitor<I, O> v, I in) {
			throw new UnsupportedOperationException();
		}

		@Override
		public <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isGround() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsFunctionCall() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Term applySubstitution(Substitution s) {
			throw new UnsupportedOperationException();
		}

		@Override
		public Term normalize(Substitution s) throws EvaluationException {
			throw new UnsupportedOperationException();
		}

		@Override
		public void varSet(Set<Var> acc) {
			throw new UnsupportedOperationException();
		}

		@Override
		public int getId() {
			return Integer.MIN_VALUE;
		}
		
	};
	
	
	public static final Term maxTerm = new Term() {

		@Override
		public <I, O> O visit(TermVisitor<I, O> v, I in) {
			throw new UnsupportedOperationException();
		}

		@Override
		public <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isGround() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsFunctionCall() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Term applySubstitution(Substitution s) {
			throw new UnsupportedOperationException();
		}

		@Override
		public Term normalize(Substitution s) throws EvaluationException {
			throw new UnsupportedOperationException();
		}

		@Override
		public void varSet(Set<Var> acc) {
			throw new UnsupportedOperationException();
		}

		@Override
		public int getId() {
			return Integer.MAX_VALUE;
		}
		
	};
	
	private static final AtomicInteger idCnt = new AtomicInteger(Integer.MIN_VALUE);
	
	public static int nextId() {
		return idCnt.incrementAndGet();
	}
	
	public static final Comparator<Term> comparator = new Comparator<Term>() {

		@Override
		public int compare(Term o1, Term o2) {
			return Integer.compare(o1.getId(), o2.getId());
		}
		
	};

}
