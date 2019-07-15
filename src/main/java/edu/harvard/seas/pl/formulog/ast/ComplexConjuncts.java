package edu.harvard.seas.pl.formulog.ast;

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

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public final class ComplexConjuncts {

	private ComplexConjuncts() {
		throw new AssertionError("impossible");
	}
	
	public static <R extends RelationSymbol> UnificationPredicate<R> unifyWithTrue(Term t) {
		return UnificationPredicate.make(t, Constructors.trueTerm(), false);
	}
	
	public static <R extends RelationSymbol> UnificationPredicate<R> trueAtom() {
		return unifyWithTrue(Constructors.trueTerm());
	}
	
	public static interface ComplexConjunctVisitor<R extends RelationSymbol, I, O> {

		O visit(UnificationPredicate<R> unificationPredicate, I input);

		O visit(UserPredicate<R> userPredicate, I input);
		
	}
	
	public static interface ComplexConjunctExnVisitor<R extends RelationSymbol, I, O, E extends Throwable> {

		O visit(UnificationPredicate<R> unificationPredicate, I input) throws E;

		O visit(UserPredicate<R> userPredicate, I input) throws E;
		
	}
	
}
