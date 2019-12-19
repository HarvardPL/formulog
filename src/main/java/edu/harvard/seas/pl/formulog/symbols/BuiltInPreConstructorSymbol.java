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

import java.util.Arrays;
import java.util.List;

public enum BuiltInPreConstructorSymbol implements PreFunctorSymbol {

	// Bit vector constructors

	BV_CONST("bv_const", 1, ParamType.NAT),

	BV_BIG_CONST("bv_big_const", 1, ParamType.NAT),

	BV_TO_BV_SIGNED("bv_to_bv_signed", 1, ParamType.NAT, ParamType.NAT),

	BV_TO_BV_UNSIGNED("bv_to_bv_unsigned", 1, ParamType.NAT, ParamType.NAT),

	FP_TO_BV("fp_to_bv", 1, ParamType.NAT, ParamType.NAT, ParamType.NAT),
	
	// Floating point constructors

	FP_CONST("fp_const", 1, ParamType.NAT, ParamType.NAT),

	FP_BIG_CONST("fp_big_const", 1, ParamType.NAT, ParamType.NAT),

	FP_TO_FP("fp_to_fp", 1, ParamType.NAT, ParamType.NAT, ParamType.NAT, ParamType.NAT),
	
	BV_TO_FP("bv_to_fp", 1, ParamType.NAT, ParamType.NAT, ParamType.NAT),
	
	;
	
	private final String name;
	private final int arity;
	private final List<ParamType> paramTypes;

	private BuiltInPreConstructorSymbol(String name, int arity, ParamType... paramTypes) {
		this.name = name;
		this.arity = arity;
		this.paramTypes = Arrays.asList(paramTypes);
	}

	@Override
	public int getArity() {
		return arity;
	}
	
	@Override
	public String getName() {
		return name;
	}

	@Override
	public List<ParamType> getParamTypes() {
		return paramTypes;
	}
	
}
