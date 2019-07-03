package edu.harvard.seas.pl.formulog.eval;

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
