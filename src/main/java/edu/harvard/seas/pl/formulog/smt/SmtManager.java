package edu.harvard.seas.pl.formulog.smt;

import java.util.ArrayList;
import java.util.List;

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

import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

public abstract class SmtManager {

	// queue-N
	// perThread-N (eventually)
	// bestMatch-N
	
	public abstract Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm assertion, int timeout) throws EvaluationException;

	protected List<SmtLibTerm> breakIntoConjuncts(SmtLibTerm assertion) {
		List<SmtLibTerm> l = new ArrayList<>();
		breakIntoConjuncts(assertion, l);
		return l;
	}
	
	private void breakIntoConjuncts(SmtLibTerm assertion, List<SmtLibTerm> acc) {
		Constructor c = (Constructor) assertion;
		ConstructorSymbol sym = c.getSymbol();
		Term[] args = c.getArgs();
		if (sym.equals(BuiltInConstructorSymbol.FORMULA_AND)) {
			breakIntoConjuncts((SmtLibTerm) args[0], acc);
			breakIntoConjuncts((SmtLibTerm) args[1], acc);
			return;
		}
		if (sym.equals(BuiltInConstructorSymbol.FORMULA_NOT)) {
			c = (Constructor) args[0];
			sym = c.getSymbol();
			args = c.getArgs();
			if (sym.equals(BuiltInConstructorSymbol.FORMULA_IMP)) {
				// Turn ~(A => B) into A /\ ~B
				breakIntoConjuncts((SmtLibTerm) args[0], acc);
				breakIntoConjuncts(negate(args[1]), acc);
				return;
			}
			if (sym.equals(BuiltInConstructorSymbol.FORMULA_OR)) {
				// Turn ~(A \/ B) to ~A /\ ~B
				breakIntoConjuncts(negate(args[0]), acc);
				breakIntoConjuncts(negate(args[1]), acc);
				return;
			}
		}
		acc.add(assertion);
	}
	
	private SmtLibTerm negate(Term t) {
		return (SmtLibTerm) Constructors.make(BuiltInConstructorSymbol.FORMULA_NOT, Terms.singletonArray(t));
	}

}
