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

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;

public class CustomFunctionDef implements FunctionDef {

	private final Symbol sym;
	private final Var[] params;
	private volatile Term body;

	private CustomFunctionDef(Symbol sym, Var[] params, Term body) {
		this.sym = sym;
		this.params = params;
		this.body = body;
	}

	public Var[] getParams() {
		return params;
	}

	public Term getBody() {
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
			return body.normalize(s);
		} catch (EvaluationException e) {
			throw new EvaluationException("Error evaluating function " + sym + ": " + e.getMessage());
		}
	}

	public static CustomFunctionDef get(Symbol sym, Var[] params, Term body) {
		return new CustomFunctionDef(sym, params, body);
	}

	public static MatchExpr getMatchExpr(Term matchee, List<MatchClause> match) {
		return new MatchExpr(matchee, match);
	}

	public static MatchClause getMatchClause(Term lhs, Term rhs) {
		return new MatchClause(lhs, rhs);
	}

	public static class MatchExpr implements Expr {

		private final Term matchee;
		private final List<MatchClause> match;

		private MatchExpr(Term matchee, List<MatchClause> match) {
			this.matchee = matchee;
			this.match = match;
		}

		public Term getMatchee() {
			return matchee;
		}

		public List<MatchClause> getClauses() {
			return match;
		}

		@Override
		public <I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

		@Override
		public Term normalize(Substitution s) throws EvaluationException {
			Term e = matchee.normalize(s);
			for (MatchClause m : match) {
				// TODO We need to create a new substitution here because we don't want our
				// previous bindings to be used in the match (since the variables in the pattern
				// shadow the previous bindings). For efficiency sake, we might want to just
				// rewrite patterns so that there is not variable shadowing.
				Substitution s2 = new SimpleSubstitution();
				if (Unification.unify(e, m.getLHS(), s2)) {
					for (Var v : s.iterateKeys()) {
						if (!s2.containsKey(v)) {
							s2.put(v, s.get(v));
						}
					}
					return m.getRHS().normalize(s2);
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
		private final Term rhs;

		private MatchClause(Term lhs, Term rhs) {
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public Term getLHS() {
			return lhs;
		}

		public Term getRHS() {
			return rhs;
		}

	}

}
