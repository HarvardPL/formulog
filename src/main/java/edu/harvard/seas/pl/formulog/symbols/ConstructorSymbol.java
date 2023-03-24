package edu.harvard.seas.pl.formulog.symbols;

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

public interface ConstructorSymbol extends TypedSymbol {

	ConstructorSymbolType getConstructorSymbolType();

	default boolean isSolverConstructorSymbol() {
		switch (getConstructorSymbolType()) {
		case SOLVER_CONSTRUCTOR_GETTER:
		case SOLVER_CONSTRUCTOR_TESTER:
		case SOLVER_EXPR:
		case SOLVER_UNINTERPRETED_FUNCTION:
		case INDEX_CONSTRUCTOR:
		case VANILLA_CONSTRUCTOR:
			return false;
		}
		throw new AssertionError("impossible");
	}

}
