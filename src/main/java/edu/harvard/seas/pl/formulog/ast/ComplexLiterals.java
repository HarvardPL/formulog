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

public final class ComplexLiterals {

	private ComplexLiterals() {
		throw new AssertionError("impossible");
	}
	
	public static UnificationPredicate unifyWithBool(Term t, boolean bool) {
		return UnificationPredicate.make(t, bool ? Constructors.trueTerm() : Constructors.falseTerm(), false);
	}
	
	public static UnificationPredicate trueAtom() {
		return unifyWithBool(Constructors.trueTerm(), true);
	}
	
	public static interface ComplexLiteralVisitor<I, O> {

		O visit(UnificationPredicate unificationPredicate, I input);

		O visit(UserPredicate userPredicate, I input);
		
	}
	
	public static interface ComplexLiteralExnVisitor<I, O, E extends Throwable> {

		O visit(UnificationPredicate unificationPredicate, I input) throws E;

		O visit(UserPredicate userPredicate, I input) throws E;
		
	}
	
}
