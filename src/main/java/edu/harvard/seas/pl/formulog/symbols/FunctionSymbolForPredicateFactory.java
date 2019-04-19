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

import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.types.Types.Type;

public class FunctionSymbolForPredicateFactory {

	private final SymbolManager symbolManager;
	
	public FunctionSymbolForPredicateFactory(SymbolManager symbolManager) {
		this.symbolManager = symbolManager;
	}

	public FunctionSymbolForPredicate create(Symbol predSym) {
		if (!predSym.getSymbolType().isRelationType()) {
			throw new IllegalArgumentException("Expected a predicate symbol, but received non-predicate symbol " + predSym);
		}
		FunctionSymbolForPredicate sym = new FunctionSymbolForPredicate(predSym);
		symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		return sym;
	}
	
	private final AtomicInteger cnt = new AtomicInteger();
	
	public class FunctionSymbolForPredicate implements Symbol {

		private final Symbol predSymbol;
		private final int id;
	
		private FunctionSymbolForPredicate(Symbol predSymbol) {
			this.predSymbol = predSymbol;
			this.id = cnt.getAndIncrement();
		}
		
		@Override
		public int getArity() {
			return predSymbol.getArity();
		}

		@Override
		public SymbolType getSymbolType() {
			return SymbolType.FUNCTION;
		}
		
		@Override
		public String toString() {
			return predSymbol + "$fun" + id;
		}

		public Symbol getPredicateSymbol() {
			return predSymbol;
		}

		@Override
		public Type getCompileTimeType() {
			return predSymbol.getCompileTimeType();
		}

	}

}
