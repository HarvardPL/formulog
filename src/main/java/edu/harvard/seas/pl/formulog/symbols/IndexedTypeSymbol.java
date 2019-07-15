package edu.harvard.seas.pl.formulog.symbols;

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
	public boolean isAlias() {
		return false;
	}
	
	@Override
	public String toString() {
		return name;
	}

	public static void registerAll(SymbolManager symbolManager) {
		for (TypeSymbol sym : IndexedTypeSymbol.values()) {
			symbolManager.registerSymbol(sym, null);
		}
	}

	@Override
	public boolean isUninterpretedSort() {
		return false;
	}

}
