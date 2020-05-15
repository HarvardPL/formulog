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


import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Util;

public class MatchExpr extends AbstractTerm implements Expr, Iterable<MatchClause> {

	private final Term matchee;
	private final List<MatchClause> match;
	private final boolean isGround;

	public static MatchExpr make(Term matchee, List<MatchClause> match) {
		return new MatchExpr(matchee, match);
	}

	MatchExpr(Term matchee, List<MatchClause> match) {
		this.matchee = matchee;
		this.match = match;
		boolean isGround = matchee.isGround();
		if (isGround) {
			for (MatchClause cl : match) {
				Set<Var> vars = cl.getRhs().varSet();
				Set<Var> patVars = cl.getLhs().varSet();
				if (!patVars.containsAll(vars)) {
					isGround = false;
					break;
				}
			}
		}
		this.isGround = isGround;
	}

	public Term getMatchee() {
		return matchee;
	}

	public List<MatchClause> getClauses() {
		return Collections.unmodifiableList(match);
	}

	@Override
	public <I, O, E extends Throwable> O accept(ExprVisitorExn<I, O, E> visitor, I in) throws E {
		return visitor.visit(this, in);
	}

	@Override
	public Term normalize(Substitution s) throws EvaluationException {
		Term e = matchee.normalize(s);
		for (MatchClause m : match) {
			if (m.tryMatch(e, s)) {
				return m.getRhs().normalize(s);
			}
		}
		if (e instanceof Constructor) {
			throw new EvaluationException("No matching pattern for " + matchee
					+ " which normalizes to a complex term with outermost constructor "
					+ ((Constructor) e).getSymbol());
		} else {
			throw new EvaluationException("No matching pattern for " + matchee + " which normalizes to the term " + e);
		}
		// throw new EvaluationException("No matching pattern for " + e + " under
		// substitution " + s);
	}

	@Override
	public <I, O> O accept(ExprVisitor<I, O> visitor, I in) {
		return visitor.visit(this, in);
	}

	@Override
	public Term applySubstitution(Substitution s) {
		if (isGround) {
			return this;
		}
		Term newMatchee = matchee.applySubstitution(s);
		List<MatchClause> clauses = new ArrayList<>();
		for (MatchClause cl : match) {
			Substitution newS = new SimpleSubstitution();
			Term pat = cl.getLhs();
			Set<Var> patVars = pat.varSet();
			for (Var x : s.iterateKeys()) {
				if (!patVars.contains(x)) {
					newS.put(x, s.get(x));
				}
			}
			Term newRhs = cl.getRhs().applySubstitution(newS);
			clauses.add(new MatchClause(pat, newRhs));
		}
		return make(newMatchee, clauses);
	}

	@Override
	public String toString() {
		String s = "match " + matchee.toString() + " with";
		for (MatchClause cl : match) {
			s += "\n\t| " + cl.getLhs() + " => " + cl.getRhs();
		}
		s += "\nend";
		return s;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((match == null) ? 0 : match.hashCode());
		result = prime * result + ((matchee == null) ? 0 : matchee.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		MatchExpr other = (MatchExpr) obj;
		if (match == null) {
			if (other.match != null)
				return false;
		} else if (!match.equals(other.match))
			return false;
		if (matchee == null) {
			if (other.matchee != null)
				return false;
		} else if (!matchee.equals(other.matchee))
			return false;
		return true;
	}

	@Override
	public boolean isGround() {
		return isGround;
	}

	@Override
	public void varSet(Set<Var> acc) {
		if (!isGround) {
			matchee.varSet(acc);
			for (MatchClause cl : match) {
				Set<Var> vars = cl.getRhs().varSet();
				vars.removeAll(cl.getLhs().varSet());
				acc.addAll(vars);
			}
		}
	}

	@Override
	public Iterator<MatchClause> iterator() {
		return match.iterator();
	}

	@Override
	public void updateVarCounts(Map<Var, Integer> counts) {
		matchee.updateVarCounts(counts);
		for (MatchClause match : this) {
			Map<Var, Integer> counts2 = new HashMap<>();
			match.getRhs().updateVarCounts(counts2);
			Set<Var> boundVars = match.getLhs().varSet();
			for (Map.Entry<Var, Integer> e : counts2.entrySet()) {
				Var x = e.getKey();
				if (!boundVars.contains(x)) {
					int n = Util.lookupOrCreate(counts, x, () -> 0);
					counts.put(x, n + e.getValue());
				}
			}
		}
	}

}
