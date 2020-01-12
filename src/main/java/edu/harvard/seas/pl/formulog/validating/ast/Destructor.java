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
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class Destructor implements SimpleLiteral {

	private final Term x;
	private final ConstructorSymbol symbol;
	private final Var[] bindings;

	public static Destructor make(Term x, ConstructorSymbol symbol, Var[] bindings) {
		assert assertDisjoint(x.varSet(), Arrays.asList(bindings)) : "A variable cannot be on both sides of a destructor";
		assert symbol.getArity() == bindings.length : "Symbol arity does not match number of variables";
		assert bindings.length == new HashSet<>(Arrays.asList(bindings)).size() : "All variables must be distinct";
		return new Destructor(x, symbol, bindings);
	}

	private static boolean assertDisjoint(Collection<Var> xs, Collection<Var> ys) {
		for (Var x : xs) {
			if (ys.contains(x)) {
				return false;
			}
		}
		return true;
	}

	private Destructor(Term x, ConstructorSymbol symbol, Var[] vars) {
		this.x = x;
		this.symbol = symbol;
		this.bindings = vars;
	}
	
	public Term getScrutinee() {
		return x;
	}
	
	public ConstructorSymbol getSymbol() {
		return symbol;
	}
	
	public Var[] getBindings() {
		return bindings;
	}

	public boolean destruct(Substitution subst) throws EvaluationException {
		Constructor ctor = (Constructor) x.normalize(subst);
		if (!ctor.getSymbol().equals(symbol)) {
			return false;
		}
		Term[] args = ctor.getArgs();
		for (int i = 0; i < args.length; ++i) {
			subst.put(bindings[i], args[i]);
		}
		return true;
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
		String s = x + " -> " + symbol + "(";
		for (int i = 0; i < bindings.length; ++i) {
			s += bindings[i];
			if (i < bindings.length - 1) {
				s += ", ";
			}
		}
		s += ")";
		return s;
	}

	@Override
	public Set<Var> varSet() {
		Set<Var> vars = new HashSet<>();
		x.varSet(vars);
		vars.addAll(Arrays.asList(bindings));
		return vars;
	}

	@Override
	public SimpleLiteralTag getTag() {
		return SimpleLiteralTag.DESTRUCTOR;
	}

	@Override
	public Term[] getArgs() {
		Term[] args = new Term[bindings.length];
		for (int i = 0; i < args.length; ++i) {
			args[i] = bindings[i];
		}
		return new Term[] { x, Constructors.make(symbol, args) };
	}
	
}
