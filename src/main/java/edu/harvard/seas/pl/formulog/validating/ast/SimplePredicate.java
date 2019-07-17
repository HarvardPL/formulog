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

import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class SimplePredicate implements SimpleConjunct {

	private final RelationSymbol symbol;
	private final Term[] args;
	private final boolean[] bindingPattern;
	private final boolean negated;

	public static SimplePredicate make(RelationSymbol symbol, Term[] args, Set<Var> boundVars, boolean negated) {
		assert symbol.getArity() == args.length : "Symbol does not match argument arity";
		boolean[] pattern = new boolean[symbol.getArity()];
		for (int i = 0; i < args.length; ++i) {
			pattern[i] = boundVars.containsAll(args[i].varSet());
		}
		return new SimplePredicate(symbol, args, pattern, negated);
	}

	private SimplePredicate(RelationSymbol symbol, Term[] args, boolean[] bindingPattern, boolean negated) {
		this.symbol = symbol;
		this.args = args;
		this.bindingPattern = bindingPattern;
		this.negated = negated;
	}

	public RelationSymbol getSymbol() {
		return symbol;
	}

	public Term[] getArgs() {
		return args;
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
		String s = "";
		if (negated) {
			s += "!";
		}
		s += symbol;
		if (args.length > 0) {
			s += "(";
			for (int i = 0; i < args.length; ++i) {
				s += args[i] + " : " + (bindingPattern[i] ? "b" : "f");
				if (i < args.length - 1) {
					s += ", ";
				}
			}
			s += ")";
		}
		return s;
	}

}
