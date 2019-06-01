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
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.cmp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.model;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.string;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.sym;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInFunctionSymbol implements Symbol {

	// i32 operations

	I32_ADD("i32_add", i32, i32, i32),

	I32_SUB("i32_sub", i32, i32, i32),

	I32_MUL("i32_mul", i32, i32, i32),

	I32_DIV("i32_div", i32, i32, i32),

	I32_REM("i32_rem", i32, i32, i32),

	I32_NEG("i32_neg", i32, i32),

	I32_LT("i32_lt", i32, i32, bool),

	I32_LE("i32_le", i32, i32, bool),

	I32_GT("i32_gt", i32, i32, bool),

	I32_GE("i32_ge", i32, i32, bool),

	I32_AND("i32_and", i32, i32, i32),

	I32_OR("i32_or", i32, i32, i32),

	I32_XOR("i32_xor", i32, i32, i32),

	// i64 operations

	I64_ADD("i64_add", i64, i64, i64),

	I64_SUB("i64_sub", i64, i64, i64),

	I64_MUL("i64_mul", i64, i64, i64),

	I64_DIV("i64_div", i64, i64, i64),

	I64_REM("i64_rem", i64, i64, i64),

	I64_NEG("i64_neg", i64, i64),

	I64_LT("i64_lt", i64, i64, bool),

	I64_LE("i64_le", i64, i64, bool),

	I64_GT("i64_gt", i64, i64, bool),

	I64_GE("i64_ge", i64, i64, bool),

	I64_AND("i64_and", i64, i64, i64),

	I64_OR("i64_or", i64, i64, i64),

	I64_XOR("i64_xor", i64, i64, i64),

	// fp32 operations

	FP32_ADD("fp32_add", fp32, fp32, fp32),

	FP32_SUB("fp32_sub", fp32, fp32, fp32),

	FP32_MUL("fp32_mul", fp32, fp32, fp32),

	FP32_DIV("fp32_div", fp32, fp32, fp32),

	FP32_REM("fp32_rem", fp32, fp32, fp32),

	FP32_NEG("fp32_neg", fp32, fp32),

	FP32_LT("fp32_lt", fp32, fp32, bool),

	FP32_LE("fp32_le", fp32, fp32, bool),

	FP32_GT("fp32_gt", fp32, fp32, bool),

	FP32_GE("fp32_ge", fp32, fp32, bool),

	FP32_EQ("fp32_eq", fp32, fp32, bool),

	// fp64 operations

	FP64_ADD("fp64_add", fp64, fp64, fp64),

	FP64_SUB("fp64_sub", fp64, fp64, fp64),

	FP64_MUL("fp64_mul", fp64, fp64, fp64),

	FP64_DIV("fp64_div", fp64, fp64, fp64),

	FP64_REM("fp64_rem", fp64, fp64, fp64),

	FP64_NEG("fp64_neg", fp64, fp64),

	FP64_LT("fp64_lt", fp64, fp64, bool),

	FP64_LE("fp64_le", fp64, fp64, bool),

	FP64_GT("fp64_gt", fp64, fp64, bool),

	FP64_GE("fp64_ge", fp64, fp64, bool),

	FP64_EQ("fp64_eq", fp64, fp64, bool),

	BEQ("beq", a, a, bool),

	BNEQ("bneq", a, a, bool),

	NEGB("negb", bool, bool),

	ANDB("andb", bool, bool, bool),

	ORB("orb", bool, bool, bool),
	
	ITE("ite", bool, a, a, a),

	STRING_OF_I32("string_of_i32", i32, string),

	STRCMP("strcmp", string, string, cmp),

	I32CMP("i32cmp", i32, i32, cmp),

	STRCAT("strcat", string, string, string),

	// Constraint solving

	IS_SAT("is_sat", smt(bool), bool),
	
	IS_VALID("is_valid", smt(bool), bool),
	
	IS_SAT_OPT("is_sat_opt", smt(bool), option(i32), option(bool)),
	
	IS_VALID_OPT("is_valid_opt", smt(bool), option(i32), option(bool)),
	
	GET_MODEL("get_model", smt(bool), option(i32), option(model)),
	
	QUERY_MODEL("query_model", sym(a), model, option(a)),
	
	SUBSTITUTE("substitute", sym(a), smt(a), smt(b), smt(b)),
	
	IS_FREE("is_free", sym(a), smt(b), bool),

	// PATH_INTERPOLANT("path_interpolant", 1, list(boolExpr), list(boolExpr)),

	// Primitive conversion

	i32ToI64("i32_to_i64", i32, i64),

	i32ToFp32("i32_to_fp32", i32, fp32),

	i32ToFp64("i32_to_fp64", i32, fp64),

	i64ToI32("i64_to_i32", i64, i32),

	i64ToFp32("i64_to_fp32", i64, fp32),

	i64ToFp64("i64_to_fp64", i64, fp64),

	fp32ToI32("fp32_to_i32", fp32, i32),

	fp32ToI64("fp32_to_i64", fp32, i64),

	fp32ToFp64("fp32_to_fp64", fp32, fp64),

	fp64ToI32("fp64_to_i32", fp64, i32),

	fp64ToI64("fp64_to_i64", fp64, i64),

	fp64ToFp32("fp64_to_fp32", fp64, fp32),
	
	// Stuff for formulas
	
	ENTER_FORMULA("enter_formula%", smt(a), smt(a)),
	
	EXIT_FORMULA("exit_formula%", a, a),
	
	// Debugging
	
	PRINT("print", a, bool)
	
	;

	private final String name;
	private final int arity;
	private final List<Type> argTypes;
	private final Type retType;

	private BuiltInFunctionSymbol(String name, Type... types) {
		this.name = name;
		this.arity = types.length - 1;
		argTypes = new ArrayList<>(Arrays.asList(types));
		retType = argTypes.remove(types.length - 1);
	}

	@Override
	public int getArity() {
		return arity;
	}

	@Override
	public SymbolType getSymbolType() {
		return SymbolType.FUNCTION;
	}

	@Override
	public String toString() {
		return name;
	}
	
	public static void registerAll(SymbolManager symbolManager) {
		for (BuiltInFunctionSymbol sym : BuiltInFunctionSymbol.values()) {
			symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		}
	}

	@Override
	public Type getCompileTimeType() {
		return new FunctorType(argTypes, retType);
	}

}
