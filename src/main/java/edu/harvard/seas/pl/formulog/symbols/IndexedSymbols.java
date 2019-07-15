package edu.harvard.seas.pl.formulog.symbols;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.util.Pair;

public final class IndexedSymbols {
	
	private IndexedSymbols() {
		throw new AssertionError("impossible");
	}

	public static Pair<IndexedTypeSymbol, List<Integer>> lookupTypeSymbol(String name, int...indices) {
		List<Integer> is = new ArrayList<>();
		for (int i : indices) {
			is.add(i);
		}
		return lookupTypeSymbol(name, is);
	}
	
	public static Pair<IndexedTypeSymbol, List<Integer>> lookupTypeSymbol(String name, List<Integer> indices) {
		IndexedTypeSymbol sym;
		try {
			sym = IndexedTypeSymbol.valueOf(name.toUpperCase());
		} catch (IllegalArgumentException e) {
			throw new IllegalArgumentException("Unrecognized symbol name: " + name);
		}
		return new Pair<>(sym, massageIndices(sym, indices));
	}
	
	public static Pair<IndexedTypeSymbol, List<Integer>> lookupConstructorSymbol(String name, int...indices) {
		List<Integer> is = new ArrayList<>();
		for (int i : indices) {
			is.add(i);
		}
		return lookupTypeSymbol(name, is);
	}
	
	public static Pair<IndexedConstructorSymbol, List<Integer>> lookupConstructorSymbol(String name, List<Integer> indices) {
		IndexedConstructorSymbol sym;
		try {
			sym = IndexedConstructorSymbol.valueOf(name.toUpperCase());
		} catch (IllegalArgumentException e) {
			throw new IllegalArgumentException("Unrecognized symbol name: " + name);
		}
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
		switch (width) {
		case 16:
			return Arrays.asList(5, 11);
		case 32:
			return Arrays.asList(8, 24);
		case 64:
			return Arrays.asList(11, 53);
		case 128:
			return Arrays.asList(15, 113);
		default:
			throw new IllegalArgumentException("Illegal FP width alias: " + width);
		}
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
			case FP_TO_BV:
				break;
			case BV_TO_FP:
			case FP_BIG_CONST:
			case FP_CONST:
			case FP_TO_FP:
			if (indices.size() == 1) {
				return expandFpAlias(indices.get(0));
			}
			break;
			}
		} else {
			throw new AssertionError("impossible");
		}
		return indices;
	}


}
