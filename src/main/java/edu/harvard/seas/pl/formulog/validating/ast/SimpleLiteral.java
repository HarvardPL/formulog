package edu.harvard.seas.pl.formulog.validating.ast;

import java.util.HashSet;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.ast.Literal;
import edu.harvard.seas.pl.formulog.ast.Var;

public interface SimpleLiteral extends Literal {

	<I, O> O accept(SimpleLiteralVisitor<I, O> visitor, I input);

	<I, O, E extends Throwable> O accept(SimpleLiteralExnVisitor<I, O, E> visitor, I input) throws E;

	default Set<Var> varSet() {
		Set<Var> vars = new HashSet<>();
		varSet(vars);
		return vars;
	}
	
	void varSet(Set<Var> vars);

	SimpleLiteralTag getTag();

}
