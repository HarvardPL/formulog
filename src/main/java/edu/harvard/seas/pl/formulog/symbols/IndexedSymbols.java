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
import java.util.List;

import edu.harvard.seas.pl.formulog.util.Pair;

public final class IndexedSymbols {

	private IndexedSymbols() {
		throw new AssertionError("impossible");
	}

	public static Pair<IndexedTypeSymbol, List<Integer>> lookupTypeSymbol(String name, SymbolManager sm,
			int... indices) {
		List<Integer> is = new ArrayList<>();
		for (int i : indices) {
			is.add(i);
		}
		return lookupTypeSymbol(name, sm, is);
	}

	public static Pair<IndexedTypeSymbol, List<Integer>> lookupTypeSymbol(String name, SymbolManager sm,
			List<Integer> indices) {
		IndexedTypeSymbol sym;
		try {
			sym = IndexedTypeSymbol.valueOf(name.toUpperCase());
		} catch (IllegalArgumentException e) {
			throw new IllegalArgumentException("Unrecognized symbol name: " + name);
		}
		sm.registerSymbol(sym);
		return new Pair<>(sym, massageIndices(sym, indices));
	}

	public static Pair<IndexedConstructorSymbol, List<Integer>> lookupConstructorSymbol(String name, SymbolManager sm,
			int... indices) {
		List<Integer> is = new ArrayList<>();
		for (int i : indices) {
			is.add(i);
		}
		return lookupConstructorSymbol(name, sm, is);
	}

	public static Pair<IndexedConstructorSymbol, List<Integer>> lookupConstructorSymbol(String name, SymbolManager sm,
			List<Integer> indices) {
		IndexedConstructorSymbol sym;
		try {
			sym = IndexedConstructorSymbol.valueOf(name.toUpperCase());
		} catch (IllegalArgumentException e) {
			throw new IllegalArgumentException("Unrecognized symbol name: " + name);
		}
		sm.registerSymbol(sym);
		return new Pair<>(sym, massageIndices(sym, indices));
	}

	private static List<Integer> massageIndices(IndexedSymbol sym, List<Integer> indices) {
		indices = expandIndices(sym, indices);
		if (indices.size() != sym.getNumExplicitIndices()) {
			throw new IllegalArgumentException("Unexpected number of indices: " + sym);
		}
		return padIndices(sym, indices);
	}

	private static List<Integer> expandFpAlias(int width) {
		List<Integer> is;
		switch (width) {
		case 16:
			is = Arrays.asList(5, 11);
			break;
		case 32:
			is = Arrays.asList(8, 24);
			break;
		case 64:
			is = Arrays.asList(11, 53);
			break;
		case 128:
			is = Arrays.asList(15, 113);
			break;
		default:
			throw new IllegalArgumentException("Illegal FP width alias: " + width);
		}
		return new ArrayList<>(is);
	}

	public static List<Integer> padIndices(IndexedSymbol sym, List<Integer> indices) {
		List<Integer> l = new ArrayList<>();
		// All padding happens at front of index list...
		for (int i = 0; i < sym.getNumImplicitIndices(); ++i) {
			l.add(null);
		}
		l.addAll(indices);
		return l;
	}

	private static List<Integer> expandIndices(IndexedSymbol sym, List<Integer> indices) {
		if (sym instanceof IndexedTypeSymbol) {
			switch ((IndexedTypeSymbol) sym) {
			case BV:
				break;
			case FP:
				if (indices.size() == 1) {
					return expandFpAlias(indices.get(0));
				}
				break;
			}
		} else if (sym instanceof IndexedConstructorSymbol) {
			switch ((IndexedConstructorSymbol) sym) {
			case BV_BIG_CONST:
			case BV_CONST:
			case BV_TO_BV_SIGNED:
			case BV_TO_BV_UNSIGNED:
				break;
			case FP_TO_BV:
				if (indices.size() == 2) {
					List<Integer> is = expandFpAlias(indices.get(0));
					is.add(indices.get(1));
					return is;
				}
				break;
			case BV_TO_FP:
				if (indices.size() == 2) {
					List<Integer> is = new ArrayList<>();
					is.add(indices.get(0));
					is.addAll(expandFpAlias(indices.get(1)));
					return is;
				}
				break;
			case FP_BIG_CONST:
			case FP_CONST:
				if (indices.size() == 1) {
					return expandFpAlias(indices.get(0));
				}
				break;
			case FP_TO_FP:
				if (indices.size() == 2) {
					List<Integer> is = expandFpAlias(indices.get(0));
					is.addAll(expandFpAlias(indices.get(1)));
					return is;
				}
				break;
			}
		} else {
			throw new AssertionError("impossible");
		}
		return indices;
	}

}
