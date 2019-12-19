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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.util.TodoException;
import edu.harvard.seas.pl.formulog.util.Util;

public enum GlobalSymbolManager {

	INSTANCE;

	private boolean initialized = false;

	private final Map<String, Symbol> memo = new ConcurrentHashMap<>();
	private final Map<String, PreSymbol> preSymbolMemo = new ConcurrentHashMap<>();
	private final Set<TypeSymbol> typeSymbols = Util.concurrentSet();

	public boolean hasName(String name) {
		checkInitialized();
		return memo.containsKey(name) || preSymbolMemo.containsKey(name);
	}

	public Symbol lookup(String name) {
		return lookup(name, Collections.emptyList());
	}

	public Symbol lookup(String name, ParamElt... params) {
		return lookup(name, Arrays.asList(params));
	}

	public Symbol lookup(String name, List<ParamElt> params) {
		checkInitialized();
		if (!hasName(name)) {
			throw new IllegalArgumentException("Unrecognized name: " + name);
		}
		if (!params.isEmpty()) {
			return lookupPreSymbol(name, params);
		}
		Symbol sym = memo.get(name);
		if (sym == null) {
			throw new IllegalArgumentException("Symbol " + name +  " is parameterized; no parameters provided.");
		}
		return sym;
	}
	
	private Symbol lookupPreSymbol(String name, List<ParamElt> params) {
		PreSymbol sym = preSymbolMemo.get(name);
		if (sym == null) {
			throw new IllegalArgumentException("Symbol " + name + " is not parameterized; parameters were provided.");
		}
		return instantiatePreSymbol(sym, params);
	}

	public Symbol instantiatePreSymbol(PreSymbol sym, ParamElt... params) {
		return instantiatePreSymbol(sym, Arrays.asList(params));
	}

	public Symbol instantiatePreSymbol(PreSymbol sym, List<ParamElt> params) {
		if (sym instanceof BuiltInPreTypeSymbol) {
			return instantiateTypePreSymbol((BuiltInPreTypeSymbol) sym, params);
		}
		assert sym instanceof BuiltInPreConstructorSymbol;
		return instantiateConstructorPreSymbol((BuiltInPreConstructorSymbol) sym, params);
	}

	public Symbol instantiateTypePreSymbol(BuiltInPreTypeSymbol sym, List<ParamElt> params) {
		throw new TodoException();
	}

	private Symbol instantiateConstructorPreSymbol(BuiltInPreConstructorSymbol sym, List<ParamElt> params) {
		throw new TodoException();
	}

	private void checkInitialized() {
		if (!initialized) {
			initialize();
		}
	}

	private synchronized void initialize() {
		if (initialized) {
			return;
		}
		register(BuiltInTypeSymbol.values());
		register(BuiltInConstructorSymbol.values());
		register(BuiltInFunctionSymbol.values());
		register(BuiltInConstructorTesterSymbol.values());
		register(BuiltInConstructorGetterSymbol.values());
		register(BuiltInPreTypeSymbol.values());
		register(BuiltInPreConstructorSymbol.values());
		initialized = true;
	}

	private void register(Symbol[] symbols) {
		for (Symbol sym : symbols) {
			register(sym);
		}
	}

	private void register(Symbol sym) {
		if (sym instanceof TypeSymbol) {
			typeSymbols.add((TypeSymbol) sym);
		}
		Symbol other = memo.putIfAbsent(sym.getName(), sym);
		assert other == null;
	}
	
	private void register(PreSymbol[] symbols) {
		for (PreSymbol sym : symbols) {
			PreSymbol other = preSymbolMemo.putIfAbsent(sym.getName(), sym);
			assert other == null;
		}
	}

	private TypeSymbol createTypeSymbol(String name, int arity, TypeSymbolType symType) {
		initialize();
		TypeSymbol sym = new TypeSymbolImpl(name, arity, symType);
		register(sym);
		return sym;
	}
	
	private ConstructorSymbol createConstructorSymbol(String name, int arity, ConstructorSymbolType symType, FunctorType type)  {
		initialize();
		ConstructorSymbol sym = new ConstructorSymbolImpl(name, arity, symType, type);
		register(sym);
		return sym;
	}
	
	private final Map<Integer, TupleSymbol> tupleSymbolMemo = new ConcurrentHashMap<>();
	private final Map<Integer, TypeSymbol> tupleTypeSymbolMemo = new ConcurrentHashMap<>();
	
	public TupleSymbol lookupTupleSymbol(int arity) {
		instantiateTuple(arity);
		return tupleSymbolMemo.get(arity);
	}
	
	public TypeSymbol lookupTupleTypeSymbol(int arity) {
		instantiateTuple(arity);
		return tupleTypeSymbolMemo.get(arity);
	}
	
	private void instantiateTuple(int arity) {
		TupleSymbol tupSym = tupleSymbolMemo.get(arity);
		if (tupSym != null) {
			return;
		}
		TypeSymbol typeSym = createTypeSymbol("tuple_type$" + arity, arity, TypeSymbolType.NORMAL_TYPE);
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
			String getter = "#_tuple" + arity + "_" + (i + 1);
			FunctorType ft = new FunctorType(type, ty);
			getters.add(createConstructorSymbol(getter, arity, ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER, ft));
			++i;
		}
		FunctorType ctorTy = new FunctorType(typeArgs, type);
		tupSym = new TupleSymbol(arity, ctorTy);
		ConstructorScheme cs = new ConstructorScheme(tupSym, typeArgs, getters);
		AlgebraicDataType.setConstructors(typeSym, typeVars, Collections.singleton(cs));
		tupleSymbolMemo.put(arity, tupSym);
		tupleTypeSymbolMemo.put(arity, typeSym);
	}
	
	public static class TupleSymbol implements ConstructorSymbol {

		private final int arity;
		private final FunctorType type;
	
		private TupleSymbol(int arity, FunctorType type) {
			this.arity = arity;
			this.type = type;
		}
		
		@Override
		public FunctorType getCompileTimeType() {
			return type;
		}

		@Override
		public int getArity() {
			return arity;
		}

		@Override
		public String getName() {
			return "tuple$" + arity;
		}

		@Override
		public ConstructorSymbolType getConstructorSymbolType() {
			return ConstructorSymbolType.VANILLA_CONSTRUCTOR;
		}
		
	}

	public Set<TypeSymbol> getTypeSymbols() {
		return typeSymbols;
	}
	
}
