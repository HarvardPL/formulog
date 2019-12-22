package edu.harvard.seas.pl.formulog.symbols.parameterized;

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

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;

import static edu.harvard.seas.pl.formulog.symbols.parameterized.ParamSubKind.NAT;

public enum BuiltInConstructorSymbolBase implements FunctorBase {

	// Bit vectors

	BV_NEG("bv_neg", 1, NAT),

	BV_ADD("bv_add", 2, NAT),

	BV_SUB("bv_sub", 2, NAT),

	BV_MUL("bv_mul", 2, NAT),

	BV_SDIV("bv_sdiv", 2, NAT),

	BV_SREM("bv_srem", 2, NAT),
	
	BV_UDIV("bv_udiv", 2, NAT),

	BV_UREM("bv_urem", 2, NAT),

	BV_AND("bv_and", 2, NAT),

	BV_OR("bv_or", 2, NAT),

	BV_XOR("bv_xor", 2, NAT),
	
	BV_SLT("bv_slt", 2, NAT),

	BV_SLE("bv_sle", 2, NAT),

	BV_SGT("bv_sgt", 2, NAT),

	BV_SGE("bv_sge", 2, NAT),
	
	BV_ULT("bv_ult", 2, NAT),

	BV_ULE("bv_ule", 2, NAT),

	BV_UGT("bv_ugt", 2, NAT),

	BV_UGE("bv_uge", 2, NAT),
	
	BV_CONST("bv_const", 1, NAT),

	BV_BIG_CONST("bv_big_const", 1, NAT),

	BV_TO_BV_SIGNED("bv_to_bv_signed", 1, NAT, NAT),

	BV_TO_BV_UNSIGNED("bv_to_bv_unsigned", 1, NAT, NAT),

	FP_TO_BV("fp_to_bv", 1, NAT, NAT, NAT),
	
	// Floating point

	FP_NEG("fp_neg", 1,NAT, NAT),

	FP_ADD("fp_add", 2,NAT, NAT),

	FP_SUB("fp_sub", 2,NAT, NAT),

	FP_MUL("fp_mul", 2, NAT, NAT),

	FP_DIV("fp_div", 2, NAT, NAT),

	FP_REM("fp_rem", 2, NAT, NAT),
	
	FP_EQ("fp_eq", 2, NAT, NAT),
	
	FP_LT("fp_lt", 2, NAT, NAT),

	FP_LE("fp_le", 2, NAT, NAT),

	FP_GT("fp_gt", 2, NAT, NAT),

	FP_GE("fp_ge", 2, NAT, NAT),

	FP_IS_NAN("fp_is_nan", 1, NAT, NAT),
	
	FP_CONST("fp_const", 1, NAT, NAT),

	FP_BIG_CONST("fp_big_const", 1, NAT, NAT),

	FP_TO_FP("fp_to_fp", 1, NAT, NAT, NAT, NAT),
	
	BV_TO_FP("bv_to_fp", 1, NAT, NAT, NAT),
	
	// Logical connectives
	
	SMT_FORALL("smt_forall", 2, ParamSubKind.SMT_VARS),
	
	SMT_EXISTS("smt_exists", 2, ParamSubKind.SMT_VARS),
	
	SMT_FORALL_PAT("smt_forall_pat", 3, ParamSubKind.SMT_VARS, ParamSubKind.MODEL_FREE_TYPE),
	
	SMT_EXISTS_PAT("smt_exists_pat", 3, ParamSubKind.SMT_VARS, ParamSubKind.MODEL_FREE_TYPE),
	
	SMT_EQ("smt_eq", 2, ParamSubKind.PRE_SMT_TYPE),
	
	SMT_LET("smt_let", 3, ParamSubKind.PRE_SMT_TYPE),

	// Arrays
	
	ARRAY_SELECT("array_select", 2, ParamSubKind.PRE_SMT_TYPE),
	
	ARRAY_DEFAULT("array_default", 1, ParamSubKind.PRE_SMT_TYPE),
	
	;
	
	private final String name;
	private final int arity;
	private final List<ParamSubKind> paramTypes;

	private BuiltInConstructorSymbolBase(String name, int arity, ParamSubKind... paramTypes) {
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
	public List<ParamSubKind> getParamSubKinds() {
		return paramTypes;
	}
	
	public ConstructorSymbolType getConstructorSymbolType() {
		return ConstructorSymbolType.SOLVER_EXPR;
	}
	
}
