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

import java.util.Arrays;
import java.util.HashSet;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class Destructor<R extends RelationSymbol> implements SimpleConjunct<R> {

	private final Term x;
	private final Symbol symbol;
	private final Var[] vars;

	public static <R extends RelationSymbol> Destructor<R> make(Term x, ConstructorSymbol symbol, Var[] vars) {
		assert !Arrays.asList(vars).contains(x) : "A variable cannot be on both sides of a destructor";
		assert symbol.getArity() == vars.length : "Symbol arity does not match number of variables";
		assert vars.length == new HashSet<>(Arrays.asList(vars)).size() : "All variables must be distinct";
		return new Destructor<R>(x, symbol, vars);
	}
	
	private Destructor(Term x, Symbol symbol, Var[] vars) {
		this.x = x;
		this.symbol = symbol;
		this.vars = vars;
	}

	public boolean destruct(Substitution subst) throws EvaluationException {
		Constructor ctor = (Constructor) x.normalize(subst);
		if (!ctor.getSymbol().equals(symbol)) {
			return false;
		}
		Term[] args = ctor.getArgs();
		for (int i = 0; i < args.length; ++i) {
			subst.put(vars[i], args[i]);
		}
		return true;
	}
	
	@Override
	public <I, O> O accept(SimpleConjunctVisitor<R, I, O> visitor, I input) {
		return visitor.visit(this, input);
	}

	@Override
	public <I, O, E extends Throwable> O accept(SimpleConjunctExnVisitor<R, I, O, E> visitor, I input) throws E {
		return visitor.visit(this, input);
	}

	@Override
	public String toString() {
		return "Destructor [x=" + x + ", symbol=" + symbol + ", vars=" + Arrays.toString(vars) + "]";
	}
	
}
