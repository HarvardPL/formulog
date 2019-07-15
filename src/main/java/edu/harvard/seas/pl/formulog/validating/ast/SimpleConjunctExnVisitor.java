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

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public interface SimpleConjunctExnVisitor<R extends RelationSymbol, I, O, E extends Throwable> {

	O visit(Assignment<R> assignment, I input) throws E;

	O visit(Check<R> check, I input) throws E;

	O visit(Destructor<R> destructor, I input) throws E;

	O visit(Predicate<R> predicate, I input) throws E;

}
