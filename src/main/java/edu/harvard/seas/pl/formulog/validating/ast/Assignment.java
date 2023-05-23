package edu.harvard.seas.pl.formulog.validating.ast;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2023 President and Fellows of Harvard College
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

import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class Assignment implements SimpleLiteral {

	private final Var var;
	private final Term rhs;

	public static Assignment make(Var var, Term rhs) {
		return new Assignment(var, rhs);
	}

	public Assignment(Var var, Term rhs) {
		this.var = var;
		this.rhs = rhs;
	}

	public void assign(Substitution subst) throws EvaluationException {
		subst.put(var, rhs.normalize(subst));
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
		return var + " <- " + rhs;
	}

	@Override
	public void varSet(Set<Var> vars) {
		vars.add(var);
		rhs.varSet(vars);
	}

	@Override
	public SimpleLiteralTag getTag() {
		return SimpleLiteralTag.ASSIGNMENT;
	}

	@Override
	public Term[] getArgs() {
		return new Term[] { var, rhs };
	}

	public Var getDef() {
		return var;
	}

	public Term getVal() {
		return rhs;
	}

}
