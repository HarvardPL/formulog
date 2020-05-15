package edu.harvard.seas.pl.formulog.symbols.parameterized;

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


import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;

public enum BuiltInConstructorSymbolBase implements FunctorBase {

	// Bit vectors

	BV_SLT("bv_slt", 2, ParamKind.NAT),

	BV_SLE("bv_sle", 2, ParamKind.NAT),

	BV_SGT("bv_sgt", 2, ParamKind.NAT),

	BV_SGE("bv_sge", 2, ParamKind.NAT),
	
	BV_ULT("bv_ult", 2, ParamKind.NAT),

	BV_ULE("bv_ule", 2, ParamKind.NAT),

	BV_UGT("bv_ugt", 2, ParamKind.NAT),

	BV_UGE("bv_uge", 2, ParamKind.NAT),
	
	BV_CONST("bv_const", 1, ParamKind.NAT),

	BV_BIG_CONST("bv_big_const", 1, ParamKind.NAT),

	BV_TO_BV_SIGNED("bv_to_bv_signed", 1, ParamKind.NAT, ParamKind.NAT),

	BV_TO_BV_UNSIGNED("bv_to_bv_unsigned", 1, ParamKind.NAT, ParamKind.NAT),

	FP_TO_SBV("fp_to_sbv", 1, ParamKind.NAT, ParamKind.NAT, ParamKind.NAT),
	
	FP_TO_UBV("fp_to_ubv", 1, ParamKind.NAT, ParamKind.NAT, ParamKind.NAT),
	
	// Floating point
	
	FP_EQ("fp_eq", 2, ParamKind.NAT, ParamKind.NAT),
	
	FP_LT("fp_lt", 2, ParamKind.NAT, ParamKind.NAT),

	FP_LE("fp_le", 2, ParamKind.NAT, ParamKind.NAT),

	FP_GT("fp_gt", 2, ParamKind.NAT, ParamKind.NAT),

	FP_GE("fp_ge", 2, ParamKind.NAT, ParamKind.NAT),

	FP_IS_NAN("fp_is_nan", 1, ParamKind.NAT, ParamKind.NAT),
	
	FP_CONST("fp_const", 1, ParamKind.NAT, ParamKind.NAT),

	FP_BIG_CONST("fp_big_const", 1, ParamKind.NAT, ParamKind.NAT),

	FP_TO_FP("fp_to_fp", 1, ParamKind.NAT, ParamKind.NAT, ParamKind.NAT, ParamKind.NAT),
	
	BV_TO_FP("bv_to_fp", 1, ParamKind.NAT, ParamKind.NAT, ParamKind.NAT),
	
	// Logical connectives

	SMT_PAT("smt_pat", 1, ParamKind.SMT_REPRESENTABLE_TYPE),
	
	SMT_WRAP_VAR("smt_wrap_var", 1, ParamKind.SMT_REPRESENTABLE_TYPE),
	
	SMT_EQ("smt_eq", 2, ParamKind.PRE_SMT_TYPE),
	
	SMT_LET("smt_let", 3, ParamKind.PRE_SMT_TYPE),

	// Arrays
	
	ARRAY_SELECT("array_select", 2, ParamKind.PRE_SMT_TYPE),
	
	ARRAY_DEFAULT("array_default", 1, ParamKind.PRE_SMT_TYPE),
	
	// Solver variables
	
	SMT_VAR("smt_var", 1, ParamKind.ANY_TYPE, ParamKind.PRE_SMT_TYPE),
	
	;
	
	private final String name;
	private final int arity;
	private final List<ParamKind> paramTypes;

	private BuiltInConstructorSymbolBase(String name, int arity, ParamKind... paramTypes) {
		this.name = name;
		this.arity = arity;
		this.paramTypes = Arrays.asList(paramTypes);
	}

	@Override
	public int getArity() {
		return arity;
	}
	
	@Override
	public String toString() {
		return name;
	}

	@Override
	public List<ParamKind> getParamKinds() {
		return paramTypes;
	}
	
	public ConstructorSymbolType getConstructorSymbolType() {
		return ConstructorSymbolType.SOLVER_EXPR;
	}
	
}
