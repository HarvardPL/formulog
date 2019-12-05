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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class SymbolManager {
	
	private final Map<String, Symbol> memo = new ConcurrentHashMap<>();
	private final Set<TypeSymbol> typeSymbols = Util.concurrentSet();

	private boolean initialized = false;

	public void initialize() {
		if (initialized) {
			throw new IllegalStateException("Cannot initialize symbol manager multiple times.");
		}
		registerAll(BuiltInTypeSymbol.values());
		registerAll(BuiltInConstructorSymbol.values());
		registerAll(BuiltInFunctionSymbol.values());
		registerAll(BuiltInConstructorTesterSymbol.values());
		registerAll(BuiltInConstructorGetterSymbol.values());
		registerAll(IndexedTypeSymbol.values());
		registerAll(IndexedConstructorSymbol.values());
		initialized = true;
	}

	public void assertInitialized() {
		if (!initialized) {
			throw new IllegalStateException("Symbol manager is not initialized.");
		}
	}

	public TypeSymbol createTypeSymbol(String name, int arity, TypeSymbolType st) {
		assertInitialized();
		checkNotUsed(name);
		TypeSymbol sym = new TypeSymbolImpl(name, arity, st);
		registerSymbol(sym);
		return sym;
	}

	public ConstructorSymbol createConstructorSymbol(String name, int arity, ConstructorSymbolType st,
			FunctorType type) {
		assertInitialized();
		checkNotUsed(name);
		ConstructorSymbol sym = new ConstructorSymbolImpl(name, arity, st, type);
		registerSymbol(sym);
		return sym;
	}

	public RecordSymbol createRecordSymbol(String name, int arity, FunctorType type, List<FunctionSymbol> labels) {
		assertInitialized();
		checkNotUsed(name);
		RecordSymbol sym = new RecordSymbolImpl(name, arity, type, labels);
		registerSymbol(sym);
		return sym;
	}

	public FunctionSymbol createFunctionSymbol(String name, int arity, FunctorType type) {
		assertInitialized();
		checkNotUsed(name);
		FunctionSymbol sym = new FunctionSymbolImpl(name, arity, type);
		registerSymbol(sym);
		return sym;
	}

	public MutableRelationSymbol createRelationSymbol(String name, int arity, boolean isIdb, FunctorType type) {
		assertInitialized();
		checkNotUsed(name);
		MutableRelationSymbol sym = new RelationSymbolImpl(name, arity, isIdb, type);
		registerSymbol(sym);
		return sym;
	}

	public void checkNotUsed(String name) {
		if (memo.containsKey(name)) {
			throw new IllegalArgumentException(
					"Cannot create symbol " + name + "; a symbol already exists with that name.");
		}
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

	public Pair<IndexedConstructorSymbol, List<Integer>> lookupIndexedConstructorSymbol(String name,
			List<Integer> indices) {
		assertInitialized();
		assert !indices.isEmpty();
		return IndexedSymbols.lookupConstructorSymbol(name, this, indices);
	}

	public Pair<IndexedTypeSymbol, List<Integer>> lookupIndexedTypeSymbol(String name, List<Integer> indices) {
		assertInitialized();
		assert !indices.isEmpty();
		return IndexedSymbols.lookupTypeSymbol(name, this, indices);
	}

	public ConstructorSymbol lookupTupleSymbol(int arity) {
		ConstructorSymbol sym = TupleSymbol.lookup(arity, this);
		return sym;
	}

	public TypeSymbol lookupTupleTypeSymbol(int arity) {
		TypeSymbol sym = TupleSymbol.lookupType(arity, this).getSymbol();
		return sym;
	}

	public PredicateFunctionSymbol createPredicateFunctionSymbol(RelationSymbol sym, BindingType[] bindings) {
		PredicateFunctionSymbol funcSym = PredicateFunctionSymbol.create(sym, bindings, this);
		return funcSym;
	}
	
	public PredicateFunctionSymbol createPredicateFunctionSymbolPlaceholder(RelationSymbol sym) {
		PredicateFunctionSymbol funcSym = PredicateFunctionSymbol.createPlaceholder(sym, this);
		return funcSym;
	}

	public ConstructorSymbol lookupSolverSymbol(Type type) {
		assert Types.getTypeVars(type).isEmpty();
		String name = "`symbol[" + type + "]";
		ConstructorSymbol sym = (ConstructorSymbol) memo.get(name);
		if (sym == null) {
			sym = createConstructorSymbol(name, 1, ConstructorSymbolType.SOLVER_VARIABLE,
					new FunctorType(BuiltInTypes.a, BuiltInTypes.sym(type)));
			registerSymbol(sym);
		}
		return sym;
	}

	public ConstructorSymbol lookupIndexConstructorSymbol(int index) {
		String name = "index$" + index;
		ConstructorSymbol sym = (ConstructorSymbol) memo.get(name);
		if (sym == null) {
			sym = createConstructorSymbol(name, 1, ConstructorSymbolType.INDEX_CONSTRUCTOR,
					new FunctorType(BuiltInTypes.i32, TypeIndex.make(index)));
			registerSymbol(sym);
		}
		return sym;
	}
	
	public SmtEqSymbol lookupSmtEqSymbol(Type eltType) {
		SmtEqSymbol sym = SmtEqSymbol.make(eltType);
		registerSymbol(sym);
		return sym;
	}

	private abstract class AbstractSymbol implements Symbol {

		private final String name;
		private final int arity;

		public AbstractSymbol(String name, int arity) {
			this.name = name;
			this.arity = arity;
		}

		@Override
		public int getArity() {
			return arity;
		}

		@Override
		public String toString() {
			return name;
		}

	}

	private class TypeSymbolImpl extends AbstractSymbol implements TypeSymbol {

		private final TypeSymbolType st;

		public TypeSymbolImpl(String name, int arity, TypeSymbolType st) {
			super(name, arity);
			this.st = st;
		}

		@Override
		public TypeSymbolType getTypeSymbolType() {
			return st;
		}

	}

	private abstract class AbstractTypedSymbol extends AbstractSymbol implements TypedSymbol {

		private final FunctorType type;

		public AbstractTypedSymbol(String name, int arity, FunctorType type) {
			super(name, arity);
			this.type = type;
		}

		@Override
		public FunctorType getCompileTimeType() {
			return type;
		}

	}

	private class FunctionSymbolImpl extends AbstractTypedSymbol implements FunctionSymbol {

		public FunctionSymbolImpl(String name, int arity, FunctorType type) {
			super(name, arity, type);
		}

	}

	private class ConstructorSymbolImpl extends AbstractTypedSymbol implements ConstructorSymbol {

		private final ConstructorSymbolType cst;

		public ConstructorSymbolImpl(String name, int arity, ConstructorSymbolType cst, FunctorType type) {
			super(name, arity, type);
			this.cst = cst;
		}

		@Override
		public ConstructorSymbolType getConstructorSymbolType() {
			return cst;
		}

	}

	private class RecordSymbolImpl extends AbstractTypedSymbol implements RecordSymbol {

		private final List<FunctionSymbol> labels;

		public RecordSymbolImpl(String name, int arity, FunctorType type, List<FunctionSymbol> labels) {
			super(name, arity, type);
			this.labels = labels;
		}

		@Override
		public ConstructorSymbolType getConstructorSymbolType() {
			return ConstructorSymbolType.VANILLA_CONSTRUCTOR;
		}

		@Override
		public List<FunctionSymbol> getLabels() {
			return labels;
		}

	}

	private class RelationSymbolImpl extends AbstractTypedSymbol implements MutableRelationSymbol {

		private final boolean idb;
		private boolean bottomUp;
		private boolean topDown;

		public RelationSymbolImpl(String name, int arity, boolean isIdb, FunctorType type) {
			super(name, arity, type);
			this.idb = isIdb;
		}

		@Override
		public boolean isIdbSymbol() {
			return idb;
		}

		@Override
		public synchronized boolean isBottomUp() {
			return bottomUp;
		}

		@Override
		public synchronized boolean isTopDown() {
			return topDown;
		}

		@Override
		public synchronized void setTopDown() {
			if (bottomUp) {
				throw new IllegalStateException("Relation cannot be both top-down and bottom-up");
			}
			topDown = true;
		}

		@Override
		public synchronized void setBottomUp() {
			if (topDown) {
				throw new IllegalStateException("Relation cannot be both top-down and bottom-up");
			}
			bottomUp = true;
		}

	}

	public void registerSymbol(Symbol sym) {
		if (sym instanceof TypeSymbol) {
			typeSymbols.add((TypeSymbol) sym);
		}
		Symbol sym2 = memo.putIfAbsent(sym.toString(), sym);
		if (sym2 != null && !sym2.equals(sym)) {
			throw new IllegalArgumentException(
					"Cannot register symbol " + sym + "; a different symbol is already registered with that name.");
		}
	}

	private void registerAll(Symbol[] symbols) {
		for (Symbol sym : symbols) {
			registerSymbol(sym);
		}
	}
	
	public Set<TypeSymbol> getTypeSymbols() {
		return Collections.unmodifiableSet(typeSymbols);
	}

}
