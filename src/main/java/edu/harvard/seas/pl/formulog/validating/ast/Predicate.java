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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class Predicate implements SimpleConjunct {

	private final RelationSymbol symbol;
	private final Term[] boundTerms;
	private final Var[] unboundVars;
	private final boolean[] bindingPattern;
	private final boolean negated;

	public static Predicate make(RelationSymbol symbol, Term[] args, Set<Var> boundVars, boolean negated) {
		assert symbol.getArity() == args.length : "Symbol does not match argument arity";
		List<Var> unbound = new ArrayList<>();
		List<Term> bound = new ArrayList<>();
		boolean[] pattern = new boolean[symbol.getArity()];
		int i = 0;
		for (Term t : args) {
			if ((pattern[i] = boundVars.containsAll(t.varSet()))) {
				bound.add(t);
			} else {
				assert t instanceof Var;
				Var x = (Var) t;
				assert !unbound.contains(x);
				unbound.add(x);
			}
		}
		Term[] bv = bound.toArray(new Term[0]);
		Var[] uv = unbound.toArray(new Var[0]);
		return new Predicate(symbol, bv, uv, pattern, negated);
	}

	private Predicate(RelationSymbol symbol, Term[] boundTerms, Var[] unboundVars, boolean[] bindingPattern, boolean negated) {
		this.symbol = symbol;
		this.boundTerms = boundTerms;
		this.unboundVars = unboundVars;
		this.bindingPattern = bindingPattern;
		this.negated = negated;
	}

	public RelationSymbol getSymbol() {
		return symbol;
	}

	public Term[] getBoundTerms() {
		return boundTerms;
	}

	public Var[] getUnboundVars() {
		return unboundVars;
	}

	public boolean[] getBindingPattern() {
		return bindingPattern;
	}
	
	public boolean isNegated() {
		return negated;
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
		return "Predicate [symbol=" + symbol + ", boundVars=" + Arrays.toString(boundTerms) + ", unboundVars="
				+ Arrays.toString(unboundVars) + ", bindingPattern=" + Arrays.toString(bindingPattern) + ", negated="
				+ negated + "]";
	}

}
