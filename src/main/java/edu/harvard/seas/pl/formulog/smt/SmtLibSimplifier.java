package edu.harvard.seas.pl.formulog.smt;

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

import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.FORMULA_AND;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.FORMULA_LET;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.TRUE;

import org.pcollections.HashTreePMap;
import org.pcollections.PMap;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;

public class SmtLibSimplifier {

	public SmtLibTerm simplify(SmtLibTerm term) {
		return term.visit(new TermVisitor<Void, SmtLibTerm>() {

			@Override
			public SmtLibTerm visit(Var t, Void in) {
				throw new AssertionError("impossible");
			}

			@Override
			public SmtLibTerm visit(Constructor c, Void in) {
				Term[] newArgs = Terms.map(c.getArgs(), t -> t.visit(this, in));
				if (c.getSymbol().equals(FORMULA_AND)) {
					if (isTrueTerm(newArgs[0])) {
						return (SmtLibTerm) newArgs[1];
					} else if (isTrueTerm(newArgs[1])) {
						return (SmtLibTerm) newArgs[0];
					}
				}
				if (c.getSymbol().equals(FORMULA_LET) && meetsInliningThreshold(newArgs[1])) {
					PMap<SolverVariable, SmtLibTerm> subst = HashTreePMap.singleton((SolverVariable) newArgs[0],
							(SmtLibTerm) newArgs[1]);
					return ((SmtLibTerm) newArgs[2]).substSolverTerms(subst);
				}
				return c.copyWithNewArgs(newArgs);
			}

			@Override
			public SmtLibTerm visit(Primitive<?> p, Void in) {
				return (SmtLibTerm) p;
			}

			@Override
			public SmtLibTerm visit(Expr expr, Void in) {
				throw new AssertionError("impossible");
			}

		}, null);
	}

	private static boolean isTrueTerm(Term t) {
		return t instanceof Constructor && ((Constructor) t).getSymbol().equals(TRUE);
	}

	private static boolean meetsInliningThreshold(Term t) {
		return t instanceof Primitive<?> || t instanceof SolverVariable;
	}

}
