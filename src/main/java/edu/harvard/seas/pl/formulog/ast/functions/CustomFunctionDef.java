package edu.harvard.seas.pl.formulog.ast.functions;

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

import java.util.List;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;

public class CustomFunctionDef implements FunctionDef {

	private final Symbol sym;
	private final Var[] params;
	private volatile Expr body;

	private CustomFunctionDef(Symbol sym, Var[] params, Expr body) {
		this.sym = sym;
		this.params = params;
		this.body = body;
	}

	public Var[] getParams() {
		return params;
	}

	public Expr getBody() {
		return body;
	}

	public void setBody(Expr newBody) {
		this.body = newBody;
	}

	@Override
	public Symbol getSymbol() {
		return sym;
	}

	@Override
	public Term evaluate(Term[] args, Substitution substitution) throws EvaluationException {
		Substitution s = new SimpleSubstitution();
		assert params.length == args.length;
		for (int i = 0; i < params.length; ++i) {
			s.put(params[i], args[i].applySubstitution(substitution));
		}
		try {
			return body.evaluate(s);
		} catch (EvaluationException e) {
			throw new EvaluationException("Error evaluating function " + sym + ": " + e.getMessage());
		}
	}

	public static CustomFunctionDef get(Symbol sym, Var[] params, Expr body) {
		return new CustomFunctionDef(sym, params, body);
	}

	public static MatchExpr getMatchExpr(Expr expr, List<MatchClause> match) {
		return new MatchExpr(expr, match);
	}

	public static MatchClause getMatchClause(Term lhs, Expr rhs) {
		return new MatchClause(lhs, rhs);
	}

	public static TermExpr liftTerm(Term t) {
		return new TermExpr(t);
	}

	public static interface Expr {

		<I, O> O visit(ExprVisitor<I, O> visitor, I in);

		<I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E;

		Term evaluate(Substitution s) throws EvaluationException;

	}

	public static class TermExpr implements Expr {

		private final Term t;

		private TermExpr(Term t) {
			this.t = t;
		}

		public Term getTerm() {
			return t;
		}

		@Override
		public <I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

		@Override
		public Term evaluate(Substitution s) throws EvaluationException {
			return t.visit(new TermVisitorExn<Void, Term, EvaluationException>() {

				@Override
				public Term visit(Var t, Void in) {
					assert s.containsKey(t);
					return s.get(t);
				}

				@Override
				public Term visit(Constructor t, Void in) throws EvaluationException {
					Term[] args = t.getArgs();
					Term[] newArgs = new Term[args.length];
					for (int i = 0; i < args.length; ++i) {
						newArgs[i] = args[i].visit(this, in);
					}
					return t.copyWithNewArgs(newArgs);
				}

				@Override
				public Term visit(Primitive<?> prim, Void in) {
					return prim;
				}

				@Override
				public Term visit(FunctionCall t, Void in) throws EvaluationException {
					Term[] args = t.getArgs();
					Term[] newArgs = new Term[args.length];
					for (int i = 0; i < args.length; ++i) {
						newArgs[i] = args[i].visit(this, in);
					}
					return t.evaluate(newArgs);
				}

			}, null);
		}

		@Override
		public <I, O> O visit(ExprVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}
		
		@Override
		public String toString() {
			return t.toString();
		}

	}

	public static class MatchExpr implements Expr {

		private final Expr expr;
		private final List<MatchClause> match;

		private MatchExpr(Expr expr, List<MatchClause> match) {
			this.expr = expr;
			this.match = match;
		}

		public Expr getExpr() {
			return expr;
		}

		public List<MatchClause> getClauses() {
			return match;
		}

		@Override
		public <I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

		@Override
		public Term evaluate(Substitution s) throws EvaluationException {
			Term e = expr.evaluate(s);
			for (MatchClause m : match) {
				// TODO We need to create a new substitution here because we don't want our
				// previous bindings to be used in the match (since the variables in the pattern
				// shadow the previous bindings). For efficiency sake, we might want to just
				// rewrite rules so that there is not variable shadowing.
				Substitution s2 = new SimpleSubstitution();
				if (Unification.unify(e, m.getLHS(), s2)) {
					for (Var v : s.iterateKeys()) {
						if (!s2.containsKey(v)) {
							s2.put(v, s.get(v));
						}
					}
					return m.getRHS().evaluate(s2);
				}
			}
			throw new EvaluationException("No matching pattern in function for " + e + " under substitution " + s);
		}

		@Override
		public <I, O> O visit(ExprVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

	}

	public static class MatchClause {

		private final Term lhs;
		private final Expr rhs;

		private MatchClause(Term lhs, Expr rhs) {
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public Term getLHS() {
			return lhs;
		}

		public Expr getRHS() {
			return rhs;
		}

	}

	public static interface ExprVisitor<I, O> {

		O visit(TermExpr termExpr, I in);

		O visit(MatchExpr matchExpr, I in);

	}

	public static interface ExprVisitorExn<I, O, E extends Throwable> {

		O visit(TermExpr termExpr, I in) throws E;

		O visit(MatchExpr matchExpr, I in) throws E;

	}

}
