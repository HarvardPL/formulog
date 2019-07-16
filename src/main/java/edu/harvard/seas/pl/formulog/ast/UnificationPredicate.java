package edu.harvard.seas.pl.formulog.ast;

import java.util.HashSet;
import java.util.Set;

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

import edu.harvard.seas.pl.formulog.ast.ComplexConjuncts.ComplexConjunctExnVisitor;
import edu.harvard.seas.pl.formulog.ast.ComplexConjuncts.ComplexConjunctVisitor;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class UnificationPredicate<R extends RelationSymbol> implements ComplexConjunct<R> {

	private final Term lhs;
	private final Term rhs;
	private final boolean negated;

	public static <R extends RelationSymbol> UnificationPredicate<R> make(Term lhs, Term rhs, boolean negated) {
		return new UnificationPredicate<>(lhs, rhs, negated);
	}
	
	private UnificationPredicate(Term lhs, Term rhs, boolean negated) {
		this.lhs = lhs;
		this.rhs = rhs;
		this.negated = negated;
	}
	
	public Term getLhs() {
		return lhs;
	}

	public Term getRhs() {
		return rhs;
	}

	@Override
	public ComplexConjunct<R> applySubstitution(Substitution subst) {
		Term newLhs = lhs.applySubstitution(subst);
		Term newRhs = rhs.applySubstitution(subst);
		return make(newLhs, newRhs, negated);
	}

	@Override
	public boolean isNegated() {
		return negated;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
		result = prime * result + (negated ? 1231 : 1237);
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
		UnificationPredicate<?> other = (UnificationPredicate<?>) obj;
		if (lhs == null) {
			if (other.lhs != null)
				return false;
		} else if (!lhs.equals(other.lhs))
			return false;
		if (negated != other.negated)
			return false;
		if (rhs == null) {
			if (other.rhs != null)
				return false;
		} else if (!rhs.equals(other.rhs))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return lhs + (negated ? " != " : " = ") + rhs;
	}

	@Override
	public <I, O> O accept(ComplexConjunctVisitor<R, I, O> visitor, I input) {
		return visitor.visit(this, input);
	}

	@Override
	public <I, O, E extends Throwable> O accept(ComplexConjunctExnVisitor<R, I, O, E> visitor, I input) throws E {
		return visitor.visit(this, input);
	}

	@Override
	public Set<Var> varSet() {
		Set<Var> vars = new HashSet<>();
		lhs.varSet(vars);
		rhs.varSet(vars);
		return vars;
	}

}
