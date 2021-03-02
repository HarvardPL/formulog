package edu.harvard.seas.pl.formulog.symbols;

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


import static edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType.SOLVER_EXPR;
import static edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType.VANILLA_CONSTRUCTOR;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.array;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.b;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bv;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.cmp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.int_;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smtPattern;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smtWrappedVar;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.string;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInConstructorSymbol implements ConstructorSymbol {

	// Lists
	
	NIL("nil", 0, VANILLA_CONSTRUCTOR),
	
	CONS("cons", 2, VANILLA_CONSTRUCTOR),
	
	// Options
	
	NONE("none", 0, VANILLA_CONSTRUCTOR),
	
	SOME("some", 1, VANILLA_CONSTRUCTOR),

	// Comparisons
	
	CMP_LT("cmp_lt", 0, VANILLA_CONSTRUCTOR),
	
	CMP_EQ("cmp_eq", 0, VANILLA_CONSTRUCTOR),
	
	CMP_GT("cmp_gt", 0, VANILLA_CONSTRUCTOR),

	// Constraints
	
	SMT_NOT("smt_not", 1, SOLVER_EXPR),
	
	SMT_AND("smt_and", 2, SOLVER_EXPR),
	
	SMT_OR("smt_or", 2, SOLVER_EXPR),
	
	SMT_IMP("smt_imp", 2, SOLVER_EXPR),
	
	SMT_ITE("smt_ite", 3, SOLVER_EXPR),
	
	SMT_EXISTS("smt_exists", 3, SOLVER_EXPR),
	
	SMT_FORALL("smt_forall", 3, SOLVER_EXPR),
	
	// Bit vectors
	
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
	
	BV_SHL("bv_shl", 2, SOLVER_EXPR),
	
	BV_ASHR("bv_ashr", 2, SOLVER_EXPR),
	
	BV_LSHR("bv_lshr", 2, SOLVER_EXPR),
	
	// Floating point

	FP_NEG("fp_neg", 1, SOLVER_EXPR),

	FP_ADD("fp_add", 2, SOLVER_EXPR),

	FP_SUB("fp_sub", 2, SOLVER_EXPR),

	FP_MUL("fp_mul", 2, SOLVER_EXPR),

	FP_DIV("fp_div", 2, SOLVER_EXPR),

	FP_REM("fp_rem", 2, SOLVER_EXPR),
	
	// Arrays

	ARRAY_STORE("array_store", 3, SOLVER_EXPR),
	
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
	
	ENTER_FORMULA("enter_formula", 1, VANILLA_CONSTRUCTOR),
	
	EXIT_FORMULA("exit_formula", 1, VANILLA_CONSTRUCTOR),	
	
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
		case SMT_AND:
		case SMT_OR:
		case SMT_IMP:
			return makeType(smt(bool), smt(bool), smt(bool));
		case SMT_ITE:
			return makeType(smt(bool), smt(a), smt(a), smt(a));
		case SMT_NOT:
			return makeType(smt(bool), smt(bool));
		case SMT_EXISTS:
		case SMT_FORALL:
			return makeType(list(smtWrappedVar), smt(bool), list(list(smtPattern)), smt(bool));
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
		case BV_SHL:
		case BV_ASHR:
		case BV_LSHR:
			return makeType(smt(bv(a)), smt(bv(a)), smt(bv(a)));
		case BV_NEG:
			return makeType(smt(bv(a)), smt(bv(a)));
		case FP_ADD:
		case FP_DIV:
		case FP_REM:
		case FP_SUB:
		case FP_MUL:
			return makeType(smt(fp(a, b)), smt(fp(a, b)), smt(fp(a, b)));
		case FP_NEG:
			return makeType(smt(fp(a, b)), smt(fp(a, b)));
		case ARRAY_STORE:
			return makeType(smt(array(a, b)), smt(a), smt(b), smt(array(a, b)));
		case ARRAY_CONST:
			return makeType(smt(b), smt(array(a, b)));
		case STR_AT:
			return makeType(smt(string), smt(int_), smt(string));
		case STR_CONCAT:
			return makeType(smt(string), smt(string), smt(string));
		case STR_CONTAINS:
			return makeType(smt(string), smt(string), smt(bool));
		case STR_INDEXOF:
			return makeType(smt(string), smt(string), smt(int_), smt(int_));
		case STR_LEN:
			return makeType(smt(string), smt(int_));
		case STR_PREFIXOF:
			return makeType(smt(string), smt(string), smt(bool));
		case STR_REPLACE:
			return makeType(smt(string), smt(string), smt(string), smt(string));
		case STR_SUBSTR:
			return makeType(smt(string), smt(int_), smt(int_), smt(string));
		case STR_SUFFIXOF:
			return makeType(smt(string), smt(string), smt(bool));
		case INT_ABS:
		case INT_NEG:
			return makeType(smt(int_), smt(int_));
		case INT_BIG_CONST:
			return makeType(bv(64), smt(int_));
		case INT_CONST:
			return makeType(bv(32), smt(int_));
		case INT_GE:
		case INT_GT:
		case INT_LE:
		case INT_LT:
			return makeType(smt(int_), smt(int_), smt(bool));
		case INT_ADD:
		case INT_MUL:
		case INT_MOD:
		case INT_SUB:
		case INT_DIV:
			return makeType(smt(int_), smt(int_), smt(int_));
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

	@Override
	public String toString() {
		return name;
	}

}
