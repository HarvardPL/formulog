package edu.harvard.seas.pl.formulog.validating.ast;

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

import java.util.HashSet;
import java.util.Set;


import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class Check implements SimpleLiteral {

	private final Term lhs;
	private final Term rhs;
	private final boolean negated;

	public static Check make(Term lhs, Term rhs, boolean negated) {
		return new Check(lhs, rhs, negated);
	}
	
	private Check(Term lhs, Term rhs, boolean negated) {
		this.lhs = lhs;
		this.rhs = rhs;
		this.negated = negated;
	}
	
	public boolean isNegated() {
		return negated;
	}
	
	public Term getLhs() {
		return lhs;
	}
	
	public Term getRhs() {
		return rhs;
	}
	
	public boolean check(Substitution subst) throws EvaluationException {
		Term lhs = this.lhs.normalize(subst);
		Term rhs = this.rhs.normalize(subst);
		assert lhs.isGround();
		assert !lhs.containsUnevaluatedTerm();
		assert rhs.isGround();
		assert !rhs.containsUnevaluatedTerm();
		return lhs.equals(rhs) ^ negated;
	}
	
	@Override
	public <I, O> O accept(SimpleLiteralVisitor<I, O> visitor, I input) {
		return visitor.visit(this, input);
	}

	@Override
	public <I, O, E extends Throwable> O accept(SimpleLiteralExnVisitor<I, O, E> visitor, I input) throws E {
		return visitor.visit(this, input);
	}

	@Override
	public String toString() {
		return lhs + (negated ? " != " : " = ") + rhs;
	}

	@Override
	public Set<Var> varSet() {
		Set<Var> vars = new HashSet<>();
		lhs.varSet(vars);
		rhs.varSet(vars);
		return vars;
	}

	@Override
	public SimpleLiteralTag getTag() {
		return SimpleLiteralTag.CHECK;
	}

	@Override
	public Term[] getArgs() {
		return new Term[] { lhs, rhs };
	}

}
