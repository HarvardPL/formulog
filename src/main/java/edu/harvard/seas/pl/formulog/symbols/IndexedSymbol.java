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

import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.b;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bv;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.c;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.d;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Pair;

public enum IndexedSymbol implements Symbol {

	// Bit vector constructors

	BV_CONST("bv_const", 1, 1, 0, SymbolType.SOLVER_EXPR),

	BV_BIG_CONST("bv_big_const", 1, 1, 0, SymbolType.SOLVER_EXPR),

	BV_TO_BV_SIGNED("bv_to_bv_signed", 1, 1, 1, SymbolType.SOLVER_EXPR),

	BV_TO_BV_UNSIGNED("bv_to_bv_unsigned", 1, 1, 1, SymbolType.SOLVER_EXPR),

	FP_TO_BV("fp_to_bv", 1, 1, 2, SymbolType.SOLVER_EXPR),
	
	// Floating point constructors

	FP_CONST("fp_const", 1, 2, 0, SymbolType.SOLVER_EXPR),

	FP_BIG_CONST("fp_big_const", 1, 2, 0, SymbolType.SOLVER_EXPR),

	FP_TO_FP("fp_to_fp", 1, 2, 2, SymbolType.SOLVER_EXPR),
	
	BV_TO_FP("bv_to_fp", 1, 2, 1, SymbolType.SOLVER_EXPR),
	
	// Indexed types
	
	BV("bv", 0, 1, 0, SymbolType.TYPE),

	FP("fp", 0, 2, 0, SymbolType.TYPE),
	
	;
	
	private final String name;
	private final int arity;
	private final int numExplicitIndices;
	private final int numImplicitIndices;
	private final SymbolType st;

	private IndexedSymbol(String name, int nonIndexArity, int numExplicitIndices, int numImplicitIndices, SymbolType st) {
		this.name = name;
		this.arity = nonIndexArity + numExplicitIndices + numImplicitIndices;
		this.numExplicitIndices = numExplicitIndices;
		this.numImplicitIndices = numImplicitIndices;
		this.st = st;
	}

	@Override
	public int getArity() {
		return arity;
	}

	@Override
	public SymbolType getSymbolType() {
		return st;
	}

	@Override
	public String toString() {
		return name;
	}

	@Override
	public Type getCompileTimeType() {
		switch (this) {
		case BV_CONST:
			return new FunctorType(i32, a, smt(bv(a)));
		case BV_BIG_CONST:
			return new FunctorType(i64, a, smt(bv(a)));
		case BV_TO_BV_SIGNED:
		case BV_TO_BV_UNSIGNED:
			return new FunctorType(bv(a), a, b, smt(bv(b)));
		case BV_TO_FP:
			return new FunctorType(bv(a), a, b, c, smt(fp(b, c)));
		case FP_BIG_CONST:
			return new FunctorType(fp64, a, b, smt(fp(a, b)));
		case FP_CONST:
			return new FunctorType(fp32, a, b, smt(fp(a, b)));
		case FP_TO_BV:
			return new FunctorType(fp(a, b), a, b, c, smt(bv(c)));
		case FP_TO_FP:
			return new FunctorType(fp(a, b), a, b, c, d, smt(fp(c, d)));
		case BV:
		case FP:
			return null;
		}
		throw new AssertionError("impossible");
	}
	
	private int getNumExplicitIndices() {
		return numExplicitIndices;
	}
	
	private int getNumImplicitIndices() {
		return numImplicitIndices;
	}

	public static Pair<Symbol, List<Integer>> lookup(String name, int...indices) {
		List<Integer> is = new ArrayList<>();
		for (int i : indices) {
			is.add(i);
		}
		return lookup(name, is);
	}
	
	public static Pair<Symbol, List<Integer>> lookup(String name, List<Integer> indices) {
		IndexedSymbol sym;
		try {
			sym = IndexedSymbol.valueOf(name.toUpperCase());
		} catch (IllegalArgumentException e) {
			return null;
		}
		indices = expandIndices(sym, indices);
		if (indices.size() != sym.getNumExplicitIndices()) {
			throw new IllegalArgumentException("Unexpected number of indices: " + name);
		}
		indices = padIndices(sym, indices);
		return new Pair<>(sym, indices);
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
		switch (sym) {
		case BV:
		case BV_BIG_CONST:
		case BV_CONST:
		case BV_TO_BV_SIGNED:
		case BV_TO_BV_UNSIGNED:
		case FP_TO_BV:
			break;
		case BV_TO_FP:
		case FP:
		case FP_BIG_CONST:
		case FP_CONST:
		case FP_TO_FP:
			if (indices.size() == 1) {
				return expandFpAlias(indices.get(0));
			}
			break;
		}
		return indices;
	}

	public static void registerAll(SymbolManager symbolManager) {
		for (Symbol sym : IndexedSymbol.values()) {
			symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		}
	}

}
