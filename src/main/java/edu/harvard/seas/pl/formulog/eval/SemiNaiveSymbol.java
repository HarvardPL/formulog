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

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class SemiNaiveSymbol implements RelationSymbol {

	private final RelationSymbol baseSymbol;
	private final SemiNaiveSymbolType semiNaiveType;

	private static final Map<Pair<RelationSymbol, SemiNaiveSymbolType>, SemiNaiveSymbol> memo = new ConcurrentHashMap<>();

	public static SemiNaiveSymbol make(RelationSymbol baseSymbol, SemiNaiveSymbolType semiNaiveType) {
		Pair<RelationSymbol, SemiNaiveSymbolType> key = new Pair<>(baseSymbol, semiNaiveType);
		return Util.lookupOrCreate(memo, key, () -> new SemiNaiveSymbol(baseSymbol, semiNaiveType));
	}

	private SemiNaiveSymbol(RelationSymbol baseSymbol, SemiNaiveSymbolType semiNaiveType) {
		this.baseSymbol = baseSymbol;
		this.semiNaiveType = semiNaiveType;
	}

	public Symbol getBaseSymbol() {
		return baseSymbol;
	}
	
	public SemiNaiveSymbolType getSemiNaiveSymbolType() {
		return semiNaiveType;
	}

	@Override
	public int getArity() {
		return baseSymbol.getArity();
	}

	@Override
	public FunctorType getCompileTimeType() {
		return baseSymbol.getCompileTimeType();
	}

	@Override
	public boolean isIdbSymbol() {
		return baseSymbol.isIdbSymbol();
	}

	@Override
	public boolean isBottomUp() {
		return baseSymbol.isBottomUp();
	}

	@Override
	public boolean isTopDown() {
		return baseSymbol.isTopDown();
	}
	
	@Override
	public String getName() {
		return baseSymbol + "<" + semiNaiveType + ">";
	}

}
