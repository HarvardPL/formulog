package edu.harvard.seas.pl.formulog.types;

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


import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.CMP_EQ;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.CMP_GT;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.CMP_LT;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.CONS;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.NIL;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.NONE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.SOME;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.ARRAY_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.BOOL_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.BV;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.CMP_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.FP;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.INT_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.LIST_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.MODEL_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.OPAQUE_SET;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.OPTION_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.SMT_PATTERN_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.SMT_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.SMT_WRAPPED_VAR_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.STRING_TYPE;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol.SYM_TYPE;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorGetterSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;

public final class BuiltInTypes {

	private BuiltInTypes() {
		throw new AssertionError();
	}

	public static final TypeVar a = TypeVar.fresh();
	public static final TypeVar b = TypeVar.fresh();
	public static final TypeVar c = TypeVar.fresh();
	public static final TypeVar d = TypeVar.fresh();

	public static final Type i32 = bv(32);
	public static final Type i64 = bv(64);
	public static final Type fp32 = fp(8, 24);
	public static final Type fp64 = fp(11, 53);
	public static final Type string = AlgebraicDataType.make(STRING_TYPE);
	public static final Type bool = AlgebraicDataType.make(BOOL_TYPE);
	public static final Type cmp = AlgebraicDataType.make(CMP_TYPE);
	public static final Type model = AlgebraicDataType.make(MODEL_TYPE);
	public static final Type int_ = AlgebraicDataType.make(INT_TYPE);
	public static final Type smtPattern = AlgebraicDataType.make(SMT_PATTERN_TYPE);
	public static final Type smtWrappedVar = AlgebraicDataType.make(SMT_WRAPPED_VAR_TYPE);

	static {
		// Only need to set constructors for types that should be interpreted as
		// algebraic data types in SMT-LIB.
		setCmpConstructors();
		setListConstructors();
		setOptionConstructors();
	}

	private static void setCmpConstructors() {
		ConstructorScheme gt = new ConstructorScheme(CMP_GT, Collections.emptyList(), Collections.emptyList());
		ConstructorScheme lt = new ConstructorScheme(CMP_LT, Collections.emptyList(), Collections.emptyList());
		ConstructorScheme eq = new ConstructorScheme(CMP_EQ, Collections.emptyList(), Collections.emptyList());
		AlgebraicDataType.setConstructors(CMP_TYPE, Collections.emptyList(), Arrays.asList(gt, lt, eq));
	}

	private static void setListConstructors() {
		ConstructorScheme nil = new ConstructorScheme(NIL, Collections.emptyList(), Collections.emptyList());
		List<ConstructorSymbol> consGetters = Arrays.asList(BuiltInConstructorGetterSymbol.CONS_1,
				BuiltInConstructorGetterSymbol.CONS_2);
		ConstructorScheme cons = new ConstructorScheme(CONS, Arrays.asList(a, list(a)), consGetters);
		AlgebraicDataType.setConstructors(LIST_TYPE, Collections.singletonList(a), Arrays.asList(nil, cons));
	}

	private static void setOptionConstructors() {
		ConstructorScheme none = new ConstructorScheme(NONE, Collections.emptyList(), Collections.emptyList());
		List<ConstructorSymbol> someGetters = Arrays.asList(BuiltInConstructorGetterSymbol.SOME_1);
		ConstructorScheme some = new ConstructorScheme(SOME, Collections.singletonList(a), someGetters);
		AlgebraicDataType.setConstructors(OPTION_TYPE, Collections.singletonList(a), Arrays.asList(none, some));
	}

	public static AlgebraicDataType list(Type a) {
		return AlgebraicDataType.make(LIST_TYPE, Collections.singletonList(a));
	}

	public static AlgebraicDataType option(Type a) {
		return AlgebraicDataType.make(OPTION_TYPE, Collections.singletonList(a));
	}

	public static AlgebraicDataType smt(Type a) {
		return AlgebraicDataType.make(SMT_TYPE, Collections.singletonList(a));
	}

	public static AlgebraicDataType sym(Type a) {
		return AlgebraicDataType.make(SYM_TYPE, Collections.singletonList(a));
	}
	
	public static AlgebraicDataType bv(Type a) {
		return AlgebraicDataType.make(BV, a);
	}
	
	public static AlgebraicDataType bv(int width) {
		return bv(TypeIndex.make(width));
	}
	
	public static AlgebraicDataType fp(Type a, Type b) {
		return AlgebraicDataType.make(FP, a, b);
	}

	public static AlgebraicDataType fp(int exponent, int significand) {
		return fp(TypeIndex.make(exponent), TypeIndex.make(significand));
	}

	public static AlgebraicDataType array(Type a, Type b) {
		return AlgebraicDataType.make(ARRAY_TYPE, Arrays.asList(a, b));
	}
	
	public static AlgebraicDataType opaqueSet(Type a) {
		return AlgebraicDataType.make(OPAQUE_SET, a);
	}
	
	public static AlgebraicDataType pair(Type a, Type b) {
		return AlgebraicDataType.make(GlobalSymbolManager.lookupTupleTypeSymbol(2), a, b);
	}

}
