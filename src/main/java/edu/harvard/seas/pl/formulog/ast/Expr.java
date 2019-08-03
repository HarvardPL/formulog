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

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;

public interface Expr extends Term {

	<I, O> O visit(ExprVisitor<I, O> visitor, I in);

	<I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E;

	@Override
	default <I, O> O accept(TermVisitor<I, O> visitor, I in) {
		return visitor.visit(this, in);
	}
	
	@Override
	default <I, O, E extends Throwable> O accept(TermVisitorExn<I, O, E> visitor, I in) throws E {
		return visitor.visit(this, in);
	}
	
	@Override
	default boolean containsFunctionCall() {
		return true;
	}

}
