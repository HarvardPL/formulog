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

import edu.harvard.seas.pl.formulog.types.BuiltInTypes;

public final class PreTypes {

	private PreTypes() {
		throw new AssertionError("impossible");
	}
	
	public static final PreType fp32 = new InstantiatedType(BuiltInTypes.fp32);
	public static final PreType fp64 = new InstantiatedType(BuiltInTypes.fp64);
	public static final PreType i32 = new InstantiatedType(BuiltInTypes.i32);
	public static final PreType i64 = new InstantiatedType(BuiltInTypes.i64);

	public static PreType bv(ParamElt width) {
		return new UninstantiatedType(BuiltInPreTypeSymbol.BV, width);
	}
	
	public static PreType fp(ParamElt exponent, ParamElt significand) {
		return new UninstantiatedType(BuiltInPreTypeSymbol.FP, exponent, significand);
	}

}
