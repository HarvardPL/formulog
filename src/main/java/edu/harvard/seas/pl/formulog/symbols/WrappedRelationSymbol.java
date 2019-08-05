package edu.harvard.seas.pl.formulog.symbols;

public interface WrappedRelationSymbol<R extends RelationSymbol> extends RelationSymbol {

	R getBaseSymbol();
	
}
