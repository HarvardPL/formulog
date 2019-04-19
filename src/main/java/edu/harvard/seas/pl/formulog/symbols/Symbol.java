package edu.harvard.seas.pl.formulog.symbols;

import edu.harvard.seas.pl.formulog.types.Types.Type;

public interface Symbol {
	
	int getArity();
	
	SymbolType getSymbolType();

	Type getCompileTimeType();
	
}
