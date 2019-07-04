package edu.harvard.seas.pl.formulog.eval;

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

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class SemiNaiveSymbol implements Symbol {

	private final Symbol underlyingSymbol;
	private final SemiNaiveSymbolType semiNaiveType;

	private static final Map<Pair<Symbol, SemiNaiveSymbolType>, SemiNaiveSymbol> memo = new ConcurrentHashMap<>();

	public static SemiNaiveSymbol make(Symbol underlyingSymbol, SemiNaiveSymbolType semiNaiveType) {
		Pair<Symbol, SemiNaiveSymbolType> key = new Pair<>(underlyingSymbol, semiNaiveType);
		return Util.lookupOrCreate(memo, key, () -> new SemiNaiveSymbol(underlyingSymbol, semiNaiveType));
	}

	private SemiNaiveSymbol(Symbol underlyingSymbol, SemiNaiveSymbolType semiNaiveType) {
		this.underlyingSymbol = underlyingSymbol;
		this.semiNaiveType = semiNaiveType;
	}

	public Symbol getUnderlyingSymbol() {
		return underlyingSymbol;
	}
	
	public SemiNaiveSymbolType getSemiNaiveSymbolType() {
		return semiNaiveType;
	}

	@Override
	public int getArity() {
		return underlyingSymbol.getArity();
	}

	@Override
	public SymbolType getSymbolType() {
		return underlyingSymbol.getSymbolType();
	}

	@Override
	public Type getCompileTimeType() {
		return underlyingSymbol.getCompileTimeType();
	}

	@Override
	public String toString() {
		return underlyingSymbol + "<" + semiNaiveType + ">";
	}

}
