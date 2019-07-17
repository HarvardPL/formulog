package edu.harvard.seas.pl.formulog.magic;

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

import java.util.Arrays;

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;

class AdornedSymbol implements RelationSymbol {

	private final RelationSymbol symbol;
	private final boolean[] adornment;

	public AdornedSymbol(RelationSymbol symbol, boolean[] adornment) {
		assert adornment != null;
		assert !(symbol instanceof AdornedSymbol);
		assert symbol.isIdbSymbol();
		this.symbol = symbol;
		this.adornment = adornment;
	}

	public RelationSymbol getSymbol() {
		return symbol;
	}

	public boolean[] getAdornment() {
		return adornment;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(adornment);
		result = prime * result + ((symbol == null) ? 0 : symbol.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AdornedSymbol other = (AdornedSymbol) obj;
		if (!Arrays.equals(adornment, other.adornment))
			return false;
		if (symbol == null) {
			if (other.symbol != null)
				return false;
		} else if (!symbol.equals(other.symbol))
			return false;
		return true;
	}

	@Override
	public int getArity() {
		return symbol.getArity();
	}
	
	@Override
	public String toString() {
		String s = symbol + "_";
		for (boolean b : adornment) {
			s += b ? "b" : "f";
		}
		return s;
	}

	@Override
	public FunctorType getCompileTimeType() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isIdbSymbol() {
		return true;
	}

	@Override
	public boolean isBottomUp() {
		return symbol.isBottomUp();
	}

	@Override
	public boolean isTopDown() {
		return symbol.isTopDown();
	}

}
