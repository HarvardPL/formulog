package edu.harvard.seas.pl.formulog.symbols;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.SymbolBase;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.util.TodoException;
import edu.harvard.seas.pl.formulog.util.Util;

public class SymbolManager {

	private final Map<String, Symbol> memo = new ConcurrentHashMap<>();
	private final Set<TypeSymbol> typeSymbols = Util.concurrentSet();

	public TypeSymbol createTypeSymbol(String name, int arity, TypeSymbolType st) {
		checkNotUsed(name);
		TypeSymbol sym = new TypeSymbolImpl(name, arity, st);
		registerSymbol(sym);
		return sym;
	}

	public ConstructorSymbol createConstructorSymbol(String name, int arity, ConstructorSymbolType st,
			FunctorType type) {
		checkNotUsed(name);
		ConstructorSymbol sym = new ConstructorSymbolImpl(name, arity, st, type);
		registerSymbol(sym);
		return sym;
	}

	public RecordSymbol createRecordSymbol(String name, int arity, FunctorType type, List<FunctionSymbol> labels) {
		checkNotUsed(name);
		RecordSymbol sym = new RecordSymbolImpl(name, arity, type, labels);
		registerSymbol(sym);
		return sym;
	}

	public FunctionSymbol createFunctionSymbol(String name, int arity, FunctorType type) {
		checkNotUsed(name);
		FunctionSymbol sym = new FunctionSymbolImpl(name, arity, type);
		registerSymbol(sym);
		return sym;
	}

	public MutableRelationSymbol createRelationSymbol(String name, int arity, FunctorType type) {
		checkNotUsed(name);
		MutableRelationSymbol sym = new RelationSymbolImpl(name, arity, type);
		registerSymbol(sym);
		return sym;
	}

	public void checkNotUsed(String name) {
		if (hasName(name)) {
			throw new IllegalArgumentException(
					"Cannot create symbol " + name + "; a symbol already exists with that name.");
		}
	}

	public boolean hasName(String name) {
		return memo.containsKey(name) || GlobalSymbolManager.hasName(name);
	}

	public boolean hasConstructorSymbolWithName(String name) {
		if (!hasName(name)) {
			return false;
		}
		return lookupSymbol(name) instanceof ConstructorSymbol;
	}

	public Symbol lookupSymbol(String name) {
		return lookupSymbol(name, Collections.emptyList());
	}

	public ParameterizedSymbol getParameterizedSymbol(SymbolBase base) {
		if (base instanceof BuiltInConstructorSymbolBase) {
			return GlobalSymbolManager.getParameterizedSymbol((BuiltInConstructorSymbolBase) base);
		}
		throw new TodoException();
	}

	public Symbol lookupSymbol(String name, List<Param> params) {
		if (GlobalSymbolManager.hasName(name)) {
			return GlobalSymbolManager.lookup(name, params);
		}
		if (!hasName(name)) {
			throw new IllegalArgumentException("No symbol exists with name " + name + ".");
		}
		Symbol sym = memo.get(name);
		assert sym != null;
		if (sym instanceof ParameterizedSymbol) {
			return ((ParameterizedSymbol) sym).copyWithNewArgs(params);
		} else if (!params.isEmpty()) {
			throw new IllegalArgumentException("Cannot supply parameters to non-parameterized symbol: " + sym);
		}
		return sym;
	}

	public PredicateFunctionSymbol createPredicateFunctionSymbol(RelationSymbol sym, BindingType[] bindings) {
		return PredicateFunctionSymbol.create(sym, bindings, this);
	}

	public PredicateFunctionSymbol createPredicateFunctionSymbolPlaceholder(RelationSymbol sym) {
		return PredicateFunctionSymbol.createPlaceholder(sym, this);
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

	private static class FunctionSymbolImpl extends AbstractTypedSymbol implements FunctionSymbol {

		public FunctionSymbolImpl(String name, int arity, FunctorType type) {
			super(name, arity, type);
		}

	}

	private static class RecordSymbolImpl extends AbstractTypedSymbol implements RecordSymbol {

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

	private static class RelationSymbolImpl extends AbstractTypedSymbol implements MutableRelationSymbol {

		private enum Mode {
			vanillaIdb, topDownIdb, bottomUpIdb, edb
		}

		private boolean disk;

		private Mode mode = Mode.vanillaIdb;

		public RelationSymbolImpl(String name, int arity, FunctorType type) {
			super(name, arity, type);
		}

		@Override
		public boolean isIdbSymbol() {
			return !isEdbSymbol();
		}

		@Override
		public boolean isEdbSymbol() {
			return mode == Mode.edb;
		}

		@Override
		public boolean isDisk() {
			return disk;
		}

		@Override
		public synchronized boolean isBottomUp() {
			return mode == Mode.bottomUpIdb;
		}

		@Override
		public synchronized boolean isTopDown() {
			return mode == Mode.topDownIdb;
		}

		@Override
		public synchronized void setTopDown() {
			if (mode == Mode.bottomUpIdb) {
				throw new IllegalStateException("Relation cannot be both top-down and bottom-up");
			}
			mode = Mode.topDownIdb;
		}

		@Override
		public synchronized void setBottomUp() {
			if (mode == Mode.topDownIdb) {
				throw new IllegalStateException("Relation cannot be both top-down and bottom-up");
			}
			mode = Mode.bottomUpIdb;
		}

		@Override
		public synchronized void setDisk() {
			disk = true;
		}

		@Override
		public void setEdb() {
			if (mode != Mode.edb && mode != Mode.vanillaIdb) {
				throw new IllegalStateException("Relation cannot be an EDB relation with other qualifier: " + mode);
			}
			mode = Mode.edb;
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

	public Set<TypeSymbol> getTypeSymbols() {
		Set<TypeSymbol> syms = new HashSet<>(typeSymbols);
		syms.addAll(GlobalSymbolManager.getTypeSymbols());
		return Collections.unmodifiableSet(syms);
	}

}
