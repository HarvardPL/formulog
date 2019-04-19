package edu.harvard.seas.pl.formulog.ast;

import edu.harvard.seas.pl.formulog.symbols.Symbol;

public interface Functor extends Term {

	Symbol getSymbol();
	
	Term[] getArgs();
	
	Functor copyWithNewArgs(Term[] args);
	
}
