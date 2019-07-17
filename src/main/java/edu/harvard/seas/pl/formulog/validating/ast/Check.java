package edu.harvard.seas.pl.formulog.validating.ast;

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

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class Check implements SimpleConjunct {

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
	
	public boolean check(Substitution subst) throws EvaluationException {
		Term lhs = this.lhs.normalize(subst);
		Term rhs = this.rhs.normalize(subst);
		assert lhs.isGround();
		assert !lhs.containsFunctionCall();
		assert rhs.isGround();
		assert !rhs.containsFunctionCall();
		return lhs.equals(rhs) ^ negated;
	}
	
	@Override
	public <I, O> O accept(SimpleConjunctVisitor<I, O> visitor, I input) {
		return visitor.visit(this, input);
	}

	@Override
	public <I, O, E extends Throwable> O accept(SimpleConjunctExnVisitor<I, O, E> visitor, I input) throws E {
		return visitor.visit(this, input);
	}

	@Override
	public String toString() {
		return lhs + (negated ? " != " : " = ") + rhs;
	}

}
