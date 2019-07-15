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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;

public class TupleSymbolFactory {

	private final SymbolManager symbolManager;

	public TupleSymbolFactory(SymbolManager symbolManager) {
		this.symbolManager = symbolManager;
	}

	private final Map<Integer, ConstructorSymbol> constructorMemo = new ConcurrentHashMap<>();
	private final Map<Integer, AlgebraicDataType> typeMemo = new ConcurrentHashMap<>();

	public ConstructorSymbol lookup(int arity) {
		ConstructorSymbol sym = constructorMemo.get(arity);
		if (sym == null) {
			instantiate(arity);
			return constructorMemo.get(arity);
		}
		return sym;
	}

	public AlgebraicDataType lookupType(int arity) {
		AlgebraicDataType type = typeMemo.get(arity);
		if (type == null) {
			instantiate(arity);
			return typeMemo.get(arity);
		}
		return type;
	}

	private synchronized void instantiate(int arity) {
		ConstructorSymbol tupSym = constructorMemo.get(arity);
		if (tupSym != null) {
			return;
		}
		TypeSymbol typeSym = symbolManager.createTypeSymbol("tuple$" + arity, arity, TypeSymbolType.NORMAL_TYPE);
		List<Type> typeArgs = new ArrayList<>();
		List<TypeVar> typeVars = new ArrayList<>();
		for (int i = 0; i < arity; ++i) {
			TypeVar x = TypeVar.fresh();
			typeArgs.add(x);
			typeVars.add(x);
		}
		AlgebraicDataType type = AlgebraicDataType.make(typeSym, typeArgs);
		List<ConstructorSymbol> getters = new ArrayList<>();
		int i = 0;
		for (Type ty : typeArgs) {
			String getter = "#tuple$" + arity + "_" + (i + 1);
			FunctorType ft = new FunctorType(type, ty);
			getters.add(symbolManager.createConstructorSymbol(getter, arity,
					ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER, ft));
			++i;
		}
		tupSym = symbolManager.createConstructorSymbol("Tuple$" + arity, arity, ConstructorSymbolType.TUPLE,
				new FunctorType(typeArgs, type));
		ConstructorScheme cs = new ConstructorScheme(tupSym, typeArgs, getters);
		AlgebraicDataType.setConstructors(typeSym, typeVars, Collections.singleton(cs));
		constructorMemo.put(arity, tupSym);
		typeMemo.put(arity, type);
	}

}
