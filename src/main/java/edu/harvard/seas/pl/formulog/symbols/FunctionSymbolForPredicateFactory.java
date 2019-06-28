package edu.harvard.seas.pl.formulog.symbols;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class FunctionSymbolForPredicateFactory {

	private final SymbolManager symbolManager;

	public FunctionSymbolForPredicateFactory(SymbolManager symbolManager) {
		this.symbolManager = symbolManager;
	}

	public PredicateFunctionSymbol create(Symbol predSym, boolean reify) {
		if (!predSym.getSymbolType().isRelationSym()) {
			throw new IllegalArgumentException(
					"Expected a predicate symbol, but received non-predicate symbol " + predSym);
		}
		if (predSym.getArity() == 0) {
			reify = false;
		}
		PredicateFunctionSymbol sym;
		if (reify) {
			sym = Util.lookupOrCreate(reifyMemo, predSym, () -> new ReifyPredicateSymbol(predSym));
		} else {
			sym = Util.lookupOrCreate(queryMemo, predSym, () -> new QueryPredicateSymbol(predSym));
		}
		symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		return sym;
	}

	private final Map<Symbol, PredicateFunctionSymbol> queryMemo = new HashMap<>();
	private final Map<Symbol, PredicateFunctionSymbol> reifyMemo = new HashMap<>();

	public interface PredicateFunctionSymbol extends Symbol {

		Symbol getPredicateSymbol();

		boolean isReification();

	}

	private class QueryPredicateSymbol implements PredicateFunctionSymbol {

		private final Symbol predSymbol;

		private QueryPredicateSymbol(Symbol predSymbol) {
			this.predSymbol = predSymbol;
		}

		@Override
		public int getArity() {
			return predSymbol.getArity();
		}

		@Override
		public SymbolType getSymbolType() {
			return SymbolType.FUNCTION;
		}

		@Override
		public String toString() {
			return predSymbol + "$query";
		}

		public Symbol getPredicateSymbol() {
			return predSymbol;
		}

		@Override
		public Type getCompileTimeType() {
			return predSymbol.getCompileTimeType();
		}

		@Override
		public boolean isReification() {
			return false;
		}

	}
	
	private class ReifyPredicateSymbol implements PredicateFunctionSymbol {

		private final Symbol predSymbol;
		private final FunctorType type;

		private ReifyPredicateSymbol(Symbol predSymbol) {
			assert predSymbol.getArity() != 0;
			this.predSymbol = predSymbol;
			FunctorType ft = (FunctorType) predSymbol.getCompileTimeType();
			List<Type> types = ft.getArgTypes();
			Type eltType;
			if (types.size() == 1) {
				eltType = types.get(0);
			} else {
				Symbol tupTypeSym = symbolManager.lookupTupleTypeSymbol(types.size());
				eltType = AlgebraicDataType.make(tupTypeSym, types);
			}
			type = new FunctorType(BuiltInTypes.list(eltType));
		}

		@Override
		public int getArity() {
			return 0;
		}

		@Override
		public SymbolType getSymbolType() {
			return SymbolType.FUNCTION;
		}

		@Override
		public String toString() {
			return predSymbol + "$reify";
		}

		public Symbol getPredicateSymbol() {
			return predSymbol;
		}

		@Override
		public Type getCompileTimeType() {
			return type;
		}

		@Override
		public boolean isReification() {
			return true;
		}

	}

}
