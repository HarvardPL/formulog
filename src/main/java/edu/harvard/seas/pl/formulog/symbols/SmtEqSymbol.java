//package edu.harvard.seas.pl.formulog.symbols;
//
///*-
// * #%L
// * FormuLog
// * %%
// * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
// * %%
// * Licensed under the Apache License, Version 2.0 (the "License");
// * you may not use this file except in compliance with the License.
// * You may obtain a copy of the License at
// * 
// *      http://www.apache.org/licenses/LICENSE-2.0
// * 
// * Unless required by applicable law or agreed to in writing, software
// * distributed under the License is distributed on an "AS IS" BASIS,
// * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// * See the License for the specific language governing permissions and
// * limitations under the License.
// * #L%
// */
//
//import java.util.HashMap;
//import java.util.Map;
//
//import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
//import edu.harvard.seas.pl.formulog.types.FunctorType;
//import edu.harvard.seas.pl.formulog.types.Types.Type;
//import edu.harvard.seas.pl.formulog.util.Util;
//
//public class SmtEqSymbol implements ConstructorSymbol {
//
//	private static final Map<Type, SmtEqSymbol> memo = new HashMap<>();
//
//	static synchronized SmtEqSymbol make(Type eltType) {
//		return Util.lookupOrCreate(memo, eltType, () -> new SmtEqSymbol(eltType));
//	}
//
//	private final Type eltType;
//
//	private SmtEqSymbol(Type eltType) {
//		this.eltType = eltType;
//	}
//
//	@Override
//	public FunctorType getCompileTimeType() {
//		return new FunctorType(BuiltInTypes.smt(eltType), BuiltInTypes.smt(eltType),
//				BuiltInTypes.smt(BuiltInTypes.bool));
//	}
//
//	@Override
//	public int getArity() {
//		return 2;
//	}
//
//	@Override
//	public ConstructorSymbolType getConstructorSymbolType() {
//		return ConstructorSymbolType.SOLVER_EXPR;
//	}
//
//	@Override
//	public String toString() {
//		return "smt_eq<" + eltType + ">";
//	}
//
//}
