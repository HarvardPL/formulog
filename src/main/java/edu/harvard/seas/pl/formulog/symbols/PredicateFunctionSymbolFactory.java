package edu.harvard.seas.pl.formulog.symbols;

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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class PredicateFunctionSymbolFactory {

	private final SymbolManager symbolManager;

	public PredicateFunctionSymbolFactory(SymbolManager symbolManager) {
		this.symbolManager = symbolManager;
	}

	public PredicateFunctionSymbol create(RelationSymbol predSym, boolean reify) {
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

	public interface PredicateFunctionSymbol extends FunctionSymbol {

		RelationSymbol getPredicateSymbol();

		boolean isReification();

	}

	private class QueryPredicateSymbol implements PredicateFunctionSymbol {

		private final RelationSymbol predSymbol;

		private QueryPredicateSymbol(RelationSymbol predSymbol) {
			this.predSymbol = predSymbol;
		}

		@Override
		public int getArity() {
			return predSymbol.getArity();
		}

		@Override
		public String toString() {
			return predSymbol + "$query";
		}

		public RelationSymbol getPredicateSymbol() {
			return predSymbol;
		}

		@Override
		public FunctorType getCompileTimeType() {
			return predSymbol.getCompileTimeType();
		}

		@Override
		public boolean isReification() {
			return false;
		}

	}
	
	private class ReifyPredicateSymbol implements PredicateFunctionSymbol {

		private final RelationSymbol predSymbol;
		private final FunctorType type;

		private ReifyPredicateSymbol(RelationSymbol predSymbol) {
			assert predSymbol.getArity() != 0;
			this.predSymbol = predSymbol;
			FunctorType ft = predSymbol.getCompileTimeType();
			List<Type> types = ft.getArgTypes();
			Type eltType;
			if (types.size() == 1) {
				eltType = types.get(0);
			} else {
				TypeSymbol tupTypeSym = symbolManager.lookupTupleTypeSymbol(types.size());
				eltType = AlgebraicDataType.make(tupTypeSym, types);
			}
			type = new FunctorType(BuiltInTypes.list(eltType));
		}

		@Override
		public int getArity() {
			return 0;
		}

		@Override
		public String toString() {
			return predSymbol + "$reify";
		}

		public RelationSymbol getPredicateSymbol() {
			return predSymbol;
		}

		@Override
		public FunctorType getCompileTimeType() {
			return type;
		}

		@Override
		public boolean isReification() {
			return true;
		}

	}

}
