package edu.harvard.seas.pl.formulog.magic;

import java.util.Arrays;

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.WrappedRelationSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;

class AdornedSymbol implements WrappedRelationSymbol<RelationSymbol> {

	private final RelationSymbol baseSymbol;
	private final boolean[] adornment;

	public AdornedSymbol(RelationSymbol baseSymbol, boolean[] adornment) {
		assert adornment != null;
		assert !(baseSymbol instanceof AdornedSymbol);
		assert baseSymbol.isIdbSymbol();
		this.baseSymbol = baseSymbol;
		this.adornment = adornment;
	}

	public boolean[] getAdornment() {
		return adornment;
	}

	@Override
	public String toString() {
		String s = getBaseSymbol() + "_";
		for (boolean b : adornment) {
			s += b ? "b" : "f";
		}
		return s;
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
	public FunctorType getCompileTimeType() {
		return baseSymbol.getCompileTimeType();
	}

	@Override
	public int getArity() {
		return baseSymbol.getArity();
	}

	@Override
	public RelationSymbol getBaseSymbol() {
		return baseSymbol;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(adornment);
		result = prime * result + ((baseSymbol == null) ? 0 : baseSymbol.hashCode());
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
		if (baseSymbol == null) {
			if (other.baseSymbol != null)
				return false;
		} else if (!baseSymbol.equals(other.baseSymbol))
			return false;
		return true;
	}

}
