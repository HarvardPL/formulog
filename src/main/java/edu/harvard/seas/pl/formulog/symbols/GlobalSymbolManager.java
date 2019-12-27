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
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public final class GlobalSymbolManager {

	private static final AtomicInteger cnt = new AtomicInteger();

	private GlobalSymbolManager() {
		throw new AssertionError("impossible");
	}

	private static boolean initialized = false;

	private static final Map<String, Symbol> memo = new ConcurrentHashMap<>();
	private static final Set<TypeSymbol> typeSymbols = Util.concurrentSet();

	public static boolean hasName(String name) {
		checkInitialized();
		return memo.containsKey(name);
	}

	public static Symbol lookup(String name) {
		return lookup(name, Collections.emptyList());
	}

	public static Symbol lookup(String name, Param... params) {
		return lookup(name, Arrays.asList(params));
	}

	public static Symbol lookup(String name, List<Param> params) {
		checkInitialized();
		if (!hasName(name)) {
			throw new IllegalArgumentException("Unrecognized name: " + name);
		}
		Symbol sym = memo.get(name);
		assert sym != null;
		if (sym instanceof ParameterizedSymbol) {
			sym = ((ParameterizedSymbol) sym).copyWithNewArgs(params);
		} else if (!params.isEmpty()) {
			throw new IllegalArgumentException("Cannot supply parameters to non-parameterized symbol: " + sym);
		}
		return sym;
	}
	
	public static ParameterizedConstructorSymbol getParameterizedSymbol(BuiltInConstructorSymbolBase base, List<Param> params) {
		return getParameterizedSymbol(base).copyWithNewArgs(params);
	}

	public static ParameterizedConstructorSymbol getParameterizedSymbol(BuiltInConstructorSymbolBase base) {
		initialize();
		return getParameterizedSymbolInternal(base);
	}

	private static ParameterizedConstructorSymbol getParameterizedSymbolInternal(BuiltInConstructorSymbolBase base) {
		List<Param> params = Param.instantiate(base.getParamKinds());
		return ParameterizedConstructorSymbol.mk(base, params);
	}

	private static void checkInitialized() {
		if (!initialized) {
			initialize();
		}
	}

	private synchronized static void initialize() {
		if (initialized) {
			return;
		}
		register(BuiltInTypeSymbol.values());
		register(BuiltInConstructorSymbol.values());
		register(BuiltInConstructorTesterSymbol.values());
		register(BuiltInConstructorGetterSymbol.values());
		register(BuiltInConstructorSymbolBase.values());
		register(BuiltInFunctionSymbol.values());
		initialized = true;
	}

	private static void register(Symbol[] symbols) {
		for (Symbol sym : symbols) {
			register(sym);
		}
	}

	private static void register(Symbol sym) {
		if (sym instanceof TypeSymbol) {
			typeSymbols.add((TypeSymbol) sym);
		}
		Symbol other = memo.putIfAbsent(sym.toString(), sym);
		assert other == null;
	}

	private static void register(BuiltInConstructorSymbolBase[] bases) {
		for (BuiltInConstructorSymbolBase base : bases) {
			ParameterizedConstructorSymbol sym = getParameterizedSymbolInternal(base);
			Symbol other = memo.putIfAbsent(base.toString(), sym);
			assert other == null;
		}
	}

//	private static final Map<ParameterizedSymbol, FinalizedConstructorSymbol> paramMemo = new ConcurrentHashMap<>();
//
//	public static FinalizedConstructorSymbol finalizeSymbol(BuiltInConstructorSymbolBase base, List<ParamElt> params) {
//		return finalizeSymbol(getParameterizedSymbol(base, params));
//	}
//	
//	public static FinalizedConstructorSymbol finalizeSymbol(ParameterizedConstructorSymbol paramSym) {
//		initialize();
//		FinalizedConstructorSymbol sym = paramMemo.get(paramSym);
//		if (sym != null) {
//			return sym;
//		}
//		if (!hasName(paramSym.getName())) {
//			throw new IllegalArgumentException("Unrecognized parameterized symbol: " + paramSym);
//		}
//		if (paramSym.containsParamVars()) {
//			throw new IllegalArgumentException(
//					"Cannot finalize a parameterized symbol that still contains unbound parameters: " + paramSym);
//		}
//		Pair<ParamElt, ParamSubKind> p = ParamUtil.findMismatch(paramSym.getArgs(),
//				paramSym.getBase().getParamSubKinds());
//		if (p != null) {
//			throw new IllegalArgumentException("Cannot finalize symbol " + paramSym
//					+ ": there is a mismatch between parameter kind " + p.snd() + " and argument " + p.fst());
//		}
//		sym = finalizeConstructorSymbol(paramSym);
//		FinalizedConstructorSymbol sym2 = paramMemo.putIfAbsent(paramSym, sym);
//		if (sym2 == null) {
//			register(sym);
//		} else {
//			sym = sym2;
//		}
//		return sym;
//	}
//
//	private static FinalizedConstructorSymbol finalizeConstructorSymbol(ParameterizedConstructorSymbol paramSym) {
//		String name = paramSym.getName() + "$" + cnt.getAndIncrement();
//		return new FinalizedConstructorSymbol() {
//
//			@Override
//			public List<ParamElt> getArgs() {
//				return paramSym.getArgs();
//			}
//
//			@Override
//			public int getArity() {
//				return paramSym.getArity();
//			}
//
//			@Override
//			public String getName() {
//				return name;
//			}
//
//			@Override
//			public ConstructorSymbolType getConstructorSymbolType() {
//				return paramSym.getConstructorSymbolType();
//			}
//
//			@Override
//			public FunctorType getCompileTimeType() {
//				return paramSym.getPreType().mkFinal();
//			}
//
//			@Override
//			public BuiltInConstructorSymbolBase getBase() {
//				return paramSym.getBase();
//			}
//			
//		};
//	}

	private static TypeSymbol createTypeSymbol(String name, int arity, TypeSymbolType symType) {
		initialize();
		TypeSymbol sym = new TypeSymbolImpl(name, arity, symType);
		register(sym);
		return sym;
	}

	private static ConstructorSymbol createConstructorSymbol(String name, int arity, ConstructorSymbolType symType,
			FunctorType type) {
		initialize();
		ConstructorSymbol sym = new ConstructorSymbolImpl(name, arity, symType, type);
		register(sym);
		return sym;
	}

	public static Set<TypeSymbol> getTypeSymbols() {
		initialize();
		return Collections.unmodifiableSet(typeSymbols);
	}

	private static final Map<Integer, TupleSymbol> tupleSymbolMemo = new ConcurrentHashMap<>();
	private static final Map<Integer, TypeSymbol> tupleTypeSymbolMemo = new ConcurrentHashMap<>();

	public static TupleSymbol lookupTupleSymbol(int arity) {
		instantiateTuple(arity);
		return tupleSymbolMemo.get(arity);
	}

	public static TypeSymbol lookupTupleTypeSymbol(int arity) {
		instantiateTuple(arity);
		return tupleTypeSymbolMemo.get(arity);
	}

	private static void instantiateTuple(int arity) {
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
		public String toString() {
			return "tuple$" + arity;
		}

		@Override
		public ConstructorSymbolType getConstructorSymbolType() {
			return ConstructorSymbolType.VANILLA_CONSTRUCTOR;
		}

	}

}
