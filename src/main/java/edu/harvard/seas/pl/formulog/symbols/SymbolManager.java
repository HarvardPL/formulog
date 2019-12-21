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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamElt;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
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

	public MutableRelationSymbol createRelationSymbol(String name, int arity, boolean isIdb, FunctorType type) {
		checkNotUsed(name);
		MutableRelationSymbol sym = new RelationSymbolImpl(name, arity, isIdb, type);
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
		return memo.containsKey(name);
	}

	public Symbol lookupSymbol(String name) {
		return lookupSymbol(name, Collections.emptyList());
	}

	public Symbol lookupSymbol(String name, List<ParamElt> params) {
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

	private class FunctionSymbolImpl extends AbstractTypedSymbol implements FunctionSymbol {

		public FunctionSymbolImpl(String name, int arity, FunctorType type) {
			super(name, arity, type);
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
		Symbol sym2 = memo.putIfAbsent(sym.getName(), sym);
		if (sym2 != null && !sym2.equals(sym)) {
			throw new IllegalArgumentException(
					"Cannot register symbol " + sym + "; a different symbol is already registered with that name.");
		}
	}

	public Set<TypeSymbol> getTypeSymbols() {
		Set<TypeSymbol> syms = new HashSet<>(typeSymbols);
		syms.addAll(GlobalSymbolManager.getTypeSymbols());
		return Collections.unmodifiableSet(typeSymbols);
	}

}
