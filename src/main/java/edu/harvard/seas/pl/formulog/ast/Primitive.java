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

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface Primitive<T> extends Term {

	T getVal();
	
	@Override
	default <I, O> O visit(TermVisitor<I, O> v, I in) {
		return v.visit(this, in);
	}

	@Override
	default <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E {
		return v.visit(this, in);
	}

	@Override
	public default boolean containsFunctionCall() {
		return false;
	}

	@Override
	public default Term applySubstitution(Substitution s) {
		return this;
	}
	
	@Override
	public default Term reduce(Substitution s) {
		return this;
	}
	
	@Override
	public default Term normalize(Substitution s) {
		return this;
	}
	
	@Override
	public default boolean isGround() {
		return true;
	}
	
	Type getType();
	
}
