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

import static edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType.SOLVER_EXPR;
import static edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType.VANILLA_CONSTRUCTOR;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.array;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.b;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bv;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.cmp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.formula_var_list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.heterogeneous_list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.int_;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.string;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.sym;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInConstructorSymbol implements ConstructorSymbol {

	// Lists
	
	NIL("nil", 0, VANILLA_CONSTRUCTOR),
	
	CONS("cons", 2, VANILLA_CONSTRUCTOR),
	
	// Options
	
	NONE("none", 0, VANILLA_CONSTRUCTOR),
	
	SOME("some", 1, VANILLA_CONSTRUCTOR),

	// Bools
	
	TRUE("true", 0, VANILLA_CONSTRUCTOR),
	
	FALSE("false", 0, VANILLA_CONSTRUCTOR),
	
	// Comparisons
	
	CMP_LT("cmp_lt", 0, VANILLA_CONSTRUCTOR),
	
	CMP_EQ("cmp_eq", 0, VANILLA_CONSTRUCTOR),
	
	CMP_GT("cmp_gt", 0, VANILLA_CONSTRUCTOR),
	
	// Constraints
	
	FORMULA_NOT("not%", 1, SOLVER_EXPR),
	
	FORMULA_AND("and%", 2, SOLVER_EXPR),
	
	FORMULA_OR("or%", 2, SOLVER_EXPR),
	
	FORMULA_EQ("eq%", 2, SOLVER_EXPR),
	
	FORMULA_IMP("imp%", 2, SOLVER_EXPR),
	
	FORMULA_LET("let%", 3, SOLVER_EXPR),
	
	FORMULA_ITE("ite%", 3, SOLVER_EXPR),
	
	FORMULA_FORALL("forall%", 3, SOLVER_EXPR),
	
	FORMULA_EXISTS("exists%", 3, SOLVER_EXPR),
	
	FORMULA_VAR_LIST_NIL("formula_var_list_nil%", 0, VANILLA_CONSTRUCTOR),
	
	FORMULA_VAR_LIST_CONS("formula_var_list_cons%", 2, VANILLA_CONSTRUCTOR),
	
	// Heterogeneous lists (used for quantifier patterns)

	HETEROGENEOUS_LIST_NIL("heterogeneous_list_nil%", 0, VANILLA_CONSTRUCTOR),
	
	HETEROGENEOUS_LIST_CONS("heterogeneous_list_cons%", 2, VANILLA_CONSTRUCTOR),
	
	// Floating point
	
	FP_NEG("fp_neg", 1,SOLVER_EXPR),

	FP_ADD("fp_add", 2,SOLVER_EXPR),

	FP_SUB("fp_sub", 2,SOLVER_EXPR),

	FP_MUL("fp_mul", 2, SOLVER_EXPR),

	FP_DIV("fp_div", 2, SOLVER_EXPR),

	FP_REM("fp_rem", 2, SOLVER_EXPR),

	FP_EQ("fp_eq", 2, SOLVER_EXPR),
	
	FP_LT("fp_lt", 2, SOLVER_EXPR),

	FP_LE("fp_le", 2, SOLVER_EXPR),

	FP_GT("fp_gt", 2, SOLVER_EXPR),

	FP_GE("fp_ge", 2, SOLVER_EXPR),

	FP_IS_NAN("fp_is_nan", 1, SOLVER_EXPR),
	
	// Bit vector

	BV_NEG("bv_neg", 1, SOLVER_EXPR),

	BV_ADD("bv_add", 2, SOLVER_EXPR),

	BV_SUB("bv_sub", 2, SOLVER_EXPR),

	BV_MUL("bv_mul", 2, SOLVER_EXPR),

	BV_SDIV("bv_sdiv", 2, SOLVER_EXPR),

	BV_SREM("bv_srem", 2, SOLVER_EXPR),
	
	BV_UDIV("bv_udiv", 2, SOLVER_EXPR),

	BV_UREM("bv_urem", 2, SOLVER_EXPR),

	BV_AND("bv_and", 2, SOLVER_EXPR),

	BV_OR("bv_or", 2, SOLVER_EXPR),

	BV_XOR("bv_xor", 2, SOLVER_EXPR),
	
	BV_SLT("bv_slt", 2, SOLVER_EXPR),

	BV_SLE("bv_sle", 2, SOLVER_EXPR),

	BV_SGT("bv_sgt", 2, SOLVER_EXPR),

	BV_SGE("bv_sge", 2, SOLVER_EXPR),
	
	BV_ULT("bv_ult", 2, SOLVER_EXPR),

	BV_ULE("bv_ule", 2, SOLVER_EXPR),

	BV_UGT("bv_ugt", 2, SOLVER_EXPR),

	BV_UGE("bv_uge", 2, SOLVER_EXPR),
	
	// Arrays

	ARRAY_SELECT("array_select", 2, SOLVER_EXPR),
	
	ARRAY_STORE("array_store", 3, SOLVER_EXPR),
	
	ARRAY_DEFAULT("array_default", 1, SOLVER_EXPR),
	
	ARRAY_CONST("array_const", 1, SOLVER_EXPR),
	
	// Strings
	
	STR_CONCAT("str_concat", 2, SOLVER_EXPR),
	
	STR_LEN("str_len", 1, SOLVER_EXPR),
	
	STR_SUBSTR("str_substr", 3, SOLVER_EXPR),
	
	STR_INDEXOF("str_indexof", 3, SOLVER_EXPR),
	
	STR_AT("str_at", 2, SOLVER_EXPR),
	
	STR_CONTAINS("str_contains", 2, SOLVER_EXPR),
	
	STR_PREFIXOF("str_prefixof", 2, SOLVER_EXPR),
	
	STR_SUFFIXOF("str_suffixof", 2, SOLVER_EXPR),
	
	STR_REPLACE("str_replace", 3, SOLVER_EXPR),
	
	// Ints
	
	INT_CONST("int_const", 1, SOLVER_EXPR),
	
	INT_BIG_CONST("int_big_const", 1, SOLVER_EXPR),
	
	INT_NEG("int_neg", 1, SOLVER_EXPR),
	
	INT_SUB("int_sub", 2, SOLVER_EXPR),

	INT_ADD("int_add", 2, SOLVER_EXPR),
	
	INT_MUL("int_mul", 2, SOLVER_EXPR),

	INT_DIV("int_div", 2, SOLVER_EXPR),
	
	INT_MOD("int_mod", 2, SOLVER_EXPR),
	
	INT_ABS("int_abs", 1, SOLVER_EXPR),
	
	INT_LE("int_le", 2, SOLVER_EXPR),
	
	INT_LT("int_lt", 2, SOLVER_EXPR),
	
	INT_GE("int_ge", 2, SOLVER_EXPR),
	
	INT_GT("int_gt", 2, SOLVER_EXPR),
	
	// Stuff for type checking formulas
	
	ENTER_FORMULA("enter_formula%", 1, VANILLA_CONSTRUCTOR),
	
	EXIT_FORMULA("exit_formula%", 1, VANILLA_CONSTRUCTOR),	
	
	;

	private final String name;
	private final int arity;
	private final ConstructorSymbolType st;
	
	private BuiltInConstructorSymbol(String name, int arity, ConstructorSymbolType st) {
		this.name = name;
		this.arity = arity;
		this.st = st;
	}

	@Override
	public int getArity() {
		return arity;
	}

	@Override
	public String toString() {
		return name;
	}

	private FunctorType makeType(Type...types) {
		assert types.length == arity + 1;
		return new FunctorType(types);
	}
	
	@Override
	public FunctorType getCompileTimeType() {
		switch (this) {
		case CMP_EQ:
		case CMP_GT:
		case CMP_LT:
			return makeType(cmp);
		case NIL:
			return makeType(list(a));
		case CONS:
			return makeType(a, list(a), list(a));
		case FALSE:
		case TRUE:
			return makeType(bool);
		case FORMULA_AND:
		case FORMULA_OR:
		case FORMULA_IMP:
			return makeType(smt(bool), smt(bool), smt(bool));
		case FORMULA_EQ:
			return makeType(smt(a), smt(a), smt(bool));
		case FORMULA_ITE:
			return makeType(smt(bool), smt(a), smt(a), smt(a));
		case FORMULA_LET:
			return makeType(sym(a), smt(a), smt(b), smt(b));
		case FORMULA_NOT:
			return makeType(smt(bool), smt(bool));
		case FORMULA_EXISTS:
			return makeType(formula_var_list, smt(bool), option(a), smt(bool));
		case FORMULA_FORALL:
			return makeType(formula_var_list, smt(bool), option(a), smt(bool));
		case FORMULA_VAR_LIST_NIL:
			return makeType(formula_var_list);
		case FORMULA_VAR_LIST_CONS:
			return makeType(sym(a), formula_var_list, formula_var_list);
		case HETEROGENEOUS_LIST_NIL:
			return makeType(heterogeneous_list);
		case HETEROGENEOUS_LIST_CONS:
			return makeType(a, heterogeneous_list, heterogeneous_list);
		case NONE:
			return makeType(option(a));
		case SOME:
			return makeType(a, option(a));
		case BV_ADD:
		case BV_AND:
		case BV_MUL:
		case BV_OR:
		case BV_SDIV:
		case BV_SREM:
		case BV_UDIV:
		case BV_UREM:
		case BV_SUB:
		case BV_XOR:
			return makeType(bv(a), bv(a), smt(bv(a)));
		case BV_NEG:
			return makeType(bv(a), smt(bv(a)));
		case BV_SGE:
		case BV_SGT:
		case BV_SLE:
		case BV_SLT:
		case BV_UGE:
		case BV_UGT:
		case BV_ULE:
		case BV_ULT:
			return makeType(bv(a), bv(a), smt(bool));
		case FP_ADD:
		case FP_DIV:
		case FP_REM:
		case FP_SUB:
		case FP_MUL:
			return makeType(fp(a, b), fp(a, b), smt(fp(a, b)));
		case FP_EQ:
		case FP_GE:
		case FP_GT:
		case FP_LE:
		case FP_LT:
			return makeType(fp(a, b), fp(a, b), smt(bool));
		case FP_IS_NAN:
			return makeType(fp(a, b), smt(bool));
		case FP_NEG:
			return makeType(fp(a, b), smt(fp(a, b)));
		case ARRAY_SELECT:
			return makeType(array(a, b), a, smt(b));
		case ARRAY_STORE:
			return makeType(array(a, b), a, b, smt(array(a, b)));
		case ARRAY_DEFAULT:
			return makeType(array(a, b), smt(b));
		case ARRAY_CONST:
			return makeType(b, smt(array(a, b)));
		case STR_AT:
			return makeType(string, int_, smt(string));
		case STR_CONCAT:
			return makeType(string, string, smt(string));
		case STR_CONTAINS:
			return makeType(string, string, smt(bool));
		case STR_INDEXOF:
			return makeType(string, string, int_, smt(int_));
		case STR_LEN:
			return makeType(string, smt(int_));
		case STR_PREFIXOF:
			return makeType(string, string, smt(bool));
		case STR_REPLACE:
			return makeType(string, string, string, smt(string));
		case STR_SUBSTR:
			return makeType(string, int_, int_, smt(string));
		case STR_SUFFIXOF:
			return makeType(string, string, smt(bool));
		case INT_ABS:
		case INT_NEG:
			return makeType(int_, smt(int_));
		case INT_BIG_CONST:
			return makeType(bv(64), smt(int_));
		case INT_CONST:
			return makeType(bv(32), smt(int_));
		case INT_GE:
		case INT_GT:
		case INT_LE:
		case INT_LT:
			return makeType(int_, int_, smt(bool));
		case INT_ADD:
		case INT_MUL:
		case INT_MOD:
		case INT_SUB:
		case INT_DIV:
			return makeType(int_, int_, smt(int_));
		case ENTER_FORMULA:
			return makeType(smt(a), smt(a));
		case EXIT_FORMULA:
			return makeType(a, a);
		}
		throw new AssertionError("impossible");
	}

	@Override
	public ConstructorSymbolType getConstructorSymbolType() {
		return st;
	}

}
