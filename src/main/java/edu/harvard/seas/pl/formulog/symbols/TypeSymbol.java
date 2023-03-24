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

public interface TypeSymbol extends Symbol {

	TypeSymbolType getTypeSymbolType();

	default boolean isNormalType() {
		return getTypeSymbolType().equals(TypeSymbolType.NORMAL_TYPE);
	}

	default boolean isAlias() {
		return getTypeSymbolType().equals(TypeSymbolType.TYPE_ALIAS);
	}

	default boolean isUninterpretedSort() {
		return getTypeSymbolType().equals(TypeSymbolType.UNINTERPRETED_SORT);
	}

}
