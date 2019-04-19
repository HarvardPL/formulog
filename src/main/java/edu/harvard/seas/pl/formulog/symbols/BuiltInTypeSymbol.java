package edu.harvard.seas.pl.formulog.symbols;

import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInTypeSymbol implements Symbol {

	BOOL_TYPE("bool", 0),

	LIST_TYPE("list", 1),

	OPTION_TYPE("option", 1),

	CMP_TYPE("cmp", 0),
	
	STRING_TYPE("string", 0),
	
	SMT_TYPE("smt", 1),
	
	SYM_TYPE("sym", 1),
	
	ARRAY_TYPE("array", 2),
	
	MODEL_TYPE("model", 0),
	
	FORMULA_VAR_LIST_TYPE("formula_var_list", 0),
	
	HETEROGENEOUS_LIST_TYPE("heterogenous_list", 0),
	
	INT_TYPE("int", 0),
	
	;

	private final String name;
	private final int arity;

	private BuiltInTypeSymbol(String name, int arity) {
		this.name = name;
		this.arity = arity;
	}

	@Override
	public int getArity() {
		return arity;
	}

	@Override
	public SymbolType getSymbolType() {
		return SymbolType.TYPE;
	}

	@Override
	public String toString() {
		return name;
	}
	
	public static void registerAll(SymbolManager symbolManager) {
		for (BuiltInTypeSymbol sym : BuiltInTypeSymbol.values()) {
			symbolManager.registerSymbol(sym, null);
		}
	}

	@Override
	public Type getCompileTimeType() {
		throw new UnsupportedOperationException("Type symbols do not themselves have types.");
	}

}
