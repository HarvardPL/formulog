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


import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import formulog.ast.Terms.TermVisitor;
import formulog.unification.SimpleSubstitution;
import formulog.unification.Substitution;
import formulog.util.Pair;


public class MatchClause {

	private final Term lhs;
	private final Term rhs;
	
	public static MatchClause make(Term lhs, Term rhs) {
		if (!checkForRepeatVariables(lhs)) {
			throw new IllegalArgumentException("Cannot repeat variables in patterns: " + lhs);
		}
		Substitution s = new SimpleSubstitution();
		for (Var x : lhs.varSet()) {
			if (!x.isUnderscore()) {
				s.put(x, Var.fresh(x.toString()));
			}
		}
		return new MatchClause(lhs.applySubstitution(s), rhs.applySubstitution(s));
	}

	private static boolean checkForRepeatVariables(Term pat) {
		return pat.accept(varsDistinct, new HashSet<>());
	}
	
	private static TermVisitor<Set<Var>, Boolean> varsDistinct = new TermVisitor<Set<Var>, Boolean>() {

		@Override
		public Boolean visit(Var x, Set<Var> in) {
			if (x.isUnderscore()) {
				return true;
			}
			return in.add(x);
		}

		@Override
		public Boolean visit(Constructor c, Set<Var> in) {
			boolean ok = true;
			for (Term t : c.getArgs()) {
				ok &= t.accept(this, in);
			}
			return ok;
		}

		@Override
		public Boolean visit(Primitive<?> p, Set<Var> in) {
			return true;
		}

		@Override
		public Boolean visit(Expr e, Set<Var> in) {
			throw new AssertionError("Shouldn't be expressions in patterns");
		}
		
	};
	
	MatchClause(Term lhs, Term rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public boolean tryMatch(Term t, Substitution s) {
		Deque<Pair<Term, Term>> stack = new ArrayDeque<>();
		stack.add(new Pair<>(lhs, t));
		while (!stack.isEmpty()) {
			Pair<Term, Term> p = stack.remove();
			Term pat = p.fst();
			Term scrutinee = p.snd();
			if (pat.equals(scrutinee)) {
				continue;
			}
			if (pat instanceof Var) {
				s.put((Var) pat, scrutinee);
			} else if (pat instanceof Primitive) {
				return false;
			} else {
				Constructor cpat = (Constructor) pat;
				Constructor cscrutinee = (Constructor) scrutinee;
				if (!cpat.getSymbol().equals(cscrutinee.getSymbol())) {
					return false;
				}
				Term[] args1 = cpat.getArgs();
				Term[] args2 = cscrutinee.getArgs();
				for (int i = 0; i < args1.length; ++i) {
					stack.add(new Pair<>(args1[i], args2[i]));
				}
			}
		}
		return true;
	}
	
	public Term getLhs() {
		return lhs;
	}

	public Term getRhs() {
		return rhs;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
		result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
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
		MatchClause other = (MatchClause) obj;
		if (lhs == null) {
			if (other.lhs != null)
				return false;
		} else if (!lhs.equals(other.lhs))
			return false;
		if (rhs == null) {
			if (other.rhs != null)
				return false;
		} else if (!rhs.equals(other.rhs))
			return false;
		return true;
	}
	
}
