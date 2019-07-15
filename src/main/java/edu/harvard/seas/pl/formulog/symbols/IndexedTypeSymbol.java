package edu.harvard.seas.pl.formulog.symbols;

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

public enum IndexedTypeSymbol implements TypeSymbol, IndexedSymbol {
	
	BV("bv", 0, 1, 0),

	FP("fp", 0, 2, 0),
	
	;
	
	private final String name;
	private final int arity;
	private final int numExplicitIndices;
	private final int numImplicitIndices;

	private IndexedTypeSymbol(String name, int nonIndexArity, int numExplicitIndices, int numImplicitIndices) {
		this.name = name;
		this.arity = nonIndexArity + numExplicitIndices + numImplicitIndices;
		this.numExplicitIndices = numExplicitIndices;
		this.numImplicitIndices = numImplicitIndices;
	}

	@Override
	public int getArity() {
		return arity;
	}

	@Override
	public int getNumExplicitIndices() {
		return numExplicitIndices;
	}

	@Override
	public int getNumImplicitIndices() {
		return numImplicitIndices;
	}

	@Override
	public String toString() {
		return name;
	}

	public static void registerAll(SymbolManager symbolManager) {
		for (TypeSymbol sym : IndexedTypeSymbol.values()) {
			symbolManager.registerSymbol(sym);
		}
	}

	@Override
	public TypeSymbolType getTypeSymbolType() {
		return TypeSymbolType.NORMAL_TYPE;
	}


}
