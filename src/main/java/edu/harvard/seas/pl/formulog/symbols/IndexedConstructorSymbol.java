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

import edu.harvard.seas.pl.formulog.types.FunctorType;

public enum IndexedConstructorSymbol implements ConstructorSymbol, IndexedSymbol {

	// Bit vector constructors

	BV_CONST("bv_const", 1, 1, 0),

	BV_BIG_CONST("bv_big_const", 1, 1, 0),

	BV_TO_BV_SIGNED("bv_to_bv_signed", 1, 1, 1),

	BV_TO_BV_UNSIGNED("bv_to_bv_unsigned", 1, 1, 1),

	FP_TO_BV("fp_to_bv", 1, 1, 2),
	
	// Floating point constructors

	FP_CONST("fp_const", 1, 2, 0),

	FP_BIG_CONST("fp_big_const", 1, 2, 0),

	FP_TO_FP("fp_to_fp", 1, 2, 2),
	
	BV_TO_FP("bv_to_fp", 1, 2, 1),
	
	;
	
	private final String name;
	private final int arity;
	private final int numExplicitIndices;
	private final int numImplicitIndices;

	private IndexedConstructorSymbol(String name, int nonIndexArity, int numExplicitIndices, int numImplicitIndices) {
		this.name = name;
		this.arity = nonIndexArity + numExplicitIndices + numImplicitIndices;
		this.numExplicitIndices = numExplicitIndices;
		this.numImplicitIndices = numImplicitIndices;
	}

	@Override
	public FunctorType getCompileTimeType() {
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
		}
		throw new AssertionError("impossible");
	}

	@Override
	public int getArity() {
		return arity;
	}

	@Override
	public int getNumExplicitIndices() {
		return numExplicitIndices;
	}

	@Override
	public int getNumImplicitIndices() {
		return numImplicitIndices;
	}

	@Override
	public ConstructorSymbolType getConstructorSymbolType() {
		return ConstructorSymbolType.SOLVER_EXPR;
	}
	
	@Override
	public String toString() {
		return name;
	}

	public static void registerAll(SymbolManager symbolManager) {
		for (ConstructorSymbol sym : IndexedConstructorSymbol.values()) {
			symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		}
	}
	
}
