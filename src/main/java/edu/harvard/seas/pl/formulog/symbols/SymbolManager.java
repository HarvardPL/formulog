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

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class SymbolManager {
	private final Map<String, Symbol> memo = new HashMap<>();
	private final Map<Symbol, Type> typeOf = new HashMap<>();
	private TupleSymbolFactory tupleSymbolFactory;
	private FunctionSymbolForPredicateFactory functionSymbolForPredicateFactory;

	private boolean initialized = false;

	public void initialize() {
		if (initialized) {
			throw new IllegalStateException("Cannot initialize symbol manager multiple times.");
		}
		tupleSymbolFactory = new TupleSymbolFactory(this);
		functionSymbolForPredicateFactory = new FunctionSymbolForPredicateFactory(this);
		BuiltInTypeSymbol.registerAll(this);
		BuiltInConstructorSymbol.registerAll(this);
		BuiltInFunctionSymbol.registerAll(this);
		BuiltInPredicateSymbol.registerAll(this);
		BuiltInConstructorTesterSymbol.registerAll(this);
		BuiltInConstructorGetterSymbol.registerAll(this);
		IndexedSymbol.registerAll(this);
		initialized = true;
	}

	public void assertInitialized() {
		if (!initialized) {
			throw new IllegalStateException("Symbol manager is not initialized.");
		}
	}

	public Symbol createSymbol(String name, int arity, SymbolType st, Type type) {
		assertInitialized();
		if (memo.containsKey(name)) {
			throw new IllegalArgumentException(
					"Cannot create symbol " + name + "; a symbol already exists with that name.");
		}
		Symbol sym = new VanillaSymbol(name, arity, st);
		registerSymbol(sym, type);
		return sym;
	}
	
	public boolean hasSymbol(String name) {
		return memo.containsKey(name);
	}

	public Symbol lookupSymbol(String name) {
		assertInitialized();
		Symbol sym = memo.get(name);
		if (sym == null) {
			throw new IllegalArgumentException("No symbol exists with name " + name + ".");
		}
		if (sym instanceof IndexedSymbol) {
			throw new IllegalArgumentException("Symbol " + sym + " is indexed, but no indices provided.");
		}
		return sym;
	}

	public Pair<Symbol, List<Integer>> lookupIndexedSymbol(String name, List<Integer> indices) {
		assertInitialized();
		if (indices.isEmpty()) {
			return new Pair<>(lookupSymbol(name), Collections.emptyList());
		}
		return IndexedSymbol.lookup(name, indices);
	}

	public Symbol lookupTupleSymbol(int arity) {
		return tupleSymbolFactory.lookup(arity);
	}

	public Symbol lookupTupleTypeSymbol(int arity) {
		return tupleSymbolFactory.lookupType(arity).getSymbol();
	}

	public Symbol createFunctionSymbolForPredicate(Symbol sym) {
		return functionSymbolForPredicateFactory.create(sym);
	}

	public Symbol lookupSolverSymbol(Type type) {
		assert Types.getTypeVars(type).isEmpty();
		String name = "`symbol[" + type + "]";
		return Util.lookupOrCreate(memo, name, () -> createSymbol(name, 1, SymbolType.SOLVER_VARIABLE,
				new FunctorType(BuiltInTypes.a, BuiltInTypes.sym(type))));
	}

	private int cnt;

	public Symbol createFreshSymbol(String namePrefix, int arity, SymbolType st, Type type) {
		String name = namePrefix + cnt++;
		return createSymbol(name, arity, st, type);
	}

	public Symbol lookupIndexConstructorSymbol(int index) {
		String name = "index$" + index;
		Symbol sym = memo.get(name);
		if (sym == null) {
			sym = createSymbol(name, 1, SymbolType.INDEX_CONSTRUCTOR,
					new FunctorType(BuiltInTypes.i32, TypeIndex.make(index)));
			memo.put(name, sym);
		}
		return sym;
	}

	private class VanillaSymbol implements Symbol {

		private final String name;
		private final int arity;
		private final SymbolType st;

		public VanillaSymbol(String name, int arity, SymbolType st) {
			this.name = name;
			this.arity = arity;
			this.st = st;
		}

		@Override
		public int getArity() {
			return arity;
		}

		@Override
		public String toString() {
			return name;
		}

		@Override
		public SymbolType getSymbolType() {
			return st;
		}

		@Override
		public Type getCompileTimeType() {
			return getType(this);
		}

	}

	public void registerSymbol(Symbol sym, Type type) {
		Symbol sym2 = memo.putIfAbsent(sym.toString(), sym);
		if (sym2 != null && !sym2.equals(sym)) {
			throw new IllegalArgumentException(
					"Cannot register symbol " + sym + "; a different symbol is already registered with that name.");
		}
		if (type == null) {
			if (!sym.getSymbolType().isTypeOrTypeAliasSymbol()) {
				throw new IllegalArgumentException("Must register a type for non-type symbol " + sym + ".");
			}
		} else {
			if (sym.getSymbolType().isTypeOrTypeAliasSymbol()) {
				throw new IllegalArgumentException(
						"Cannot register type for symbol " + sym + " since it represents a type.");
			}
			Type type2 = typeOf.putIfAbsent(sym, type);
			if (type2 != null && !type2.equals(type)) {
				throw new IllegalArgumentException("Cannot register multiple types for the same symbol " + sym + ".");
			}
		}
	}

	public Type getType(Symbol sym) {
		Type type = typeOf.get(sym);
		if (type == null) {
			throw new NoSuchElementException("No type associated with symbol " + sym);
		}
		return type;
	}

}
