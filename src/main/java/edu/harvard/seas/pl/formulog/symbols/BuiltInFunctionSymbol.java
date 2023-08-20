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

import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.cmp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.model;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.opaqueSet;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.pair;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.string;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.sym;

import edu.harvard.seas.pl.formulog.types.FunctorType;

public enum BuiltInFunctionSymbol implements FunctionSymbol {

  // i32 operations

  I32_ADD("i32_add", 2),

  I32_SUB("i32_sub", 2),

  I32_MUL("i32_mul", 2),

  I32_SDIV("i32_sdiv", 2),

  I32_SREM("i32_srem", 2),

  I32_UDIV("i32_udiv", 2),

  I32_UREM("i32_urem", 2),

  I32_NEG("i32_neg", 1),

  I32_LT("i32_lt", 2),

  I32_LE("i32_le", 2),

  I32_GT("i32_gt", 2),

  I32_GE("i32_ge", 2),

  I32_AND("i32_and", 2),

  I32_OR("i32_or", 2),

  I32_XOR("i32_xor", 2),

  I32_SCMP("i32_scmp", 2),

  I32_UCMP("i32_ucmp", 2),

  I32_SHL("i32_shl", 2),

  I32_ASHR("i32_ashr", 2),

  I32_LSHR("i32_lshr", 2),

  // i64 operations

  I64_ADD("i64_add", 2),

  I64_SUB("i64_sub", 2),

  I64_MUL("i64_mul", 2),

  I64_SDIV("i64_sdiv", 2),

  I64_SREM("i64_srem", 2),

  I64_UDIV("i64_udiv", 2),

  I64_UREM("i64_urem", 2),

  I64_NEG("i64_neg", 1),

  I64_LT("i64_lt", 2),

  I64_LE("i64_le", 2),

  I64_GT("i64_gt", 2),

  I64_GE("i64_ge", 2),

  I64_AND("i64_and", 2),

  I64_OR("i64_or", 2),

  I64_XOR("i64_xor", 2),

  I64_SCMP("i64_scmp", 2),

  I64_UCMP("i64_ucmp", 2),

  I64_SHL("i64_shl", 2),

  I64_ASHR("i64_ashr", 2),

  I64_LSHR("i64_lshr", 2),

  // fp32 operations

  FP32_ADD("fp32_add", 2),

  FP32_SUB("fp32_sub", 2),

  FP32_MUL("fp32_mul", 2),

  FP32_DIV("fp32_div", 2),

  FP32_REM("fp32_rem", 2),

  FP32_NEG("fp32_neg", 1),

  FP32_LT("fp32_lt", 2),

  FP32_LE("fp32_le", 2),

  FP32_GT("fp32_gt", 2),

  FP32_GE("fp32_ge", 2),

  FP32_EQ("fp32_eq", 2),

  // fp64 operations

  FP64_ADD("fp64_add", 2),

  FP64_SUB("fp64_sub", 2),

  FP64_MUL("fp64_mul", 2),

  FP64_DIV("fp64_div", 2),

  FP64_REM("fp64_rem", 2),

  FP64_NEG("fp64_neg", 1),

  FP64_LT("fp64_lt", 2),

  FP64_LE("fp64_le", 2),

  FP64_GT("fp64_gt", 2),

  FP64_GE("fp64_ge", 2),

  FP64_EQ("fp64_eq", 2),

  // Boolean operations

  BEQ("beq", 2),

  BNEQ("bneq", 2),

  BNOT("bnot", 1),

  // String operations

  STRING_CMP("string_cmp", 2),

  STRING_CONCAT("string_concat", 2),

  STRING_MATCHES("string_matches", 2),

  STRING_STARTS_WITH("string_starts_with", 2),

  TO_STRING("to_string", 1),

  STRING_TO_LIST("string_to_list", 1),

  LIST_TO_STRING("list_to_string", 1),

  CHAR_AT("char_at", 2),

  SUBSTRING("substring", 3),

  STRING_LENGTH("string_length", 1),

  // Constraint solving

  IS_SAT("is_sat", 1),

  IS_VALID("is_valid", 1),

  IS_SAT_OPT("is_sat_opt", 2),

  GET_MODEL("get_model", 2),

  QUERY_MODEL("query_model", 2),

  IS_SET_SAT("is_set_sat", 2),

  // Opaque datatypes

  OPAQUE_SET_EMPTY("opaque_set_empty", 0),

  OPAQUE_SET_PLUS("opaque_set_plus", 2),

  OPAQUE_SET_MINUS("opaque_set_minus", 2),

  OPAQUE_SET_UNION("opaque_set_union", 2),

  OPAQUE_SET_DIFF("opaque_set_diff", 2),

  OPAQUE_SET_CHOOSE("opaque_set_choose", 1),

  OPAQUE_SET_SIZE("opaque_set_size", 1),

  OPAQUE_SET_MEMBER("opaque_set_member", 2),

  OPAQUE_SET_SINGLETON("opaque_set_singleton", 1),

  OPAQUE_SET_SUBSET("opaque_set_subset", 2),

  OPAQUE_SET_FROM_LIST("opaque_set_from_list", 1),

  // Primitive conversion

  i32ToI64("i32_to_i64", 1),

  i32ToFp32("i32_to_fp32", 1),

  i32ToFp64("i32_to_fp64", 1),

  i64ToI32("i64_to_i32", 1),

  i64ToFp32("i64_to_fp32", 1),

  i64ToFp64("i64_to_fp64", 1),

  fp32ToI32("fp32_to_i32", 1),

  fp32ToI64("fp32_to_i64", 1),

  fp32ToFp64("fp32_to_fp64", 1),

  fp64ToI32("fp64_to_i32", 1),

  fp64ToI64("fp64_to_i64", 1),

  fp64ToFp32("fp64_to_fp32", 1),

  stringToI32("string_to_i32", 1),

  stringToI64("string_to_i64", 1),

  // Debugging

  PRINT("print", 1),
  ;

  private final String name;
  private final int arity;

  BuiltInFunctionSymbol(String name, int arity) {
    this.name = name;
    this.arity = arity;
  }

  @Override
  public int getArity() {
    return arity;
  }

  @Override
  public FunctorType getCompileTimeType() {
    switch (this) {
      case BEQ:
      case BNEQ:
        return new FunctorType(a, a, bool);
      case BNOT:
        return new FunctorType(bool, bool);
      case FP32_NEG:
        return new FunctorType(fp32, fp32);
      case FP32_ADD:
      case FP32_DIV:
      case FP32_MUL:
      case FP32_REM:
      case FP32_SUB:
        return new FunctorType(fp32, fp32, fp32);
      case FP32_EQ:
      case FP32_GE:
      case FP32_GT:
      case FP32_LE:
      case FP32_LT:
        return new FunctorType(fp32, fp32, bool);
      case FP64_NEG:
        return new FunctorType(fp64, fp64);
      case FP64_ADD:
      case FP64_DIV:
      case FP64_MUL:
      case FP64_REM:
      case FP64_SUB:
        return new FunctorType(fp64, fp64, fp64);
      case FP64_EQ:
      case FP64_GE:
      case FP64_GT:
      case FP64_LE:
      case FP64_LT:
        return new FunctorType(fp64, fp64, bool);
      case GET_MODEL:
        return new FunctorType(list(smt(bool)), option(i32), option(model));
      case I32_NEG:
        return new FunctorType(i32, i32);
      case I32_ADD:
      case I32_AND:
      case I32_SDIV:
      case I32_MUL:
      case I32_OR:
      case I32_SREM:
      case I32_UDIV:
      case I32_UREM:
      case I32_SUB:
      case I32_XOR:
      case I32_SHL:
      case I32_ASHR:
      case I32_LSHR:
        return new FunctorType(i32, i32, i32);
      case I32_GE:
      case I32_GT:
      case I32_LE:
      case I32_LT:
        return new FunctorType(i32, i32, bool);
      case I32_SCMP:
      case I32_UCMP:
        return new FunctorType(i32, i32, cmp);
      case I64_NEG:
        return new FunctorType(i64, i64);
      case I64_ADD:
      case I64_AND:
      case I64_SDIV:
      case I64_MUL:
      case I64_OR:
      case I64_SREM:
      case I64_UDIV:
      case I64_UREM:
      case I64_SUB:
      case I64_XOR:
      case I64_SHL:
      case I64_ASHR:
      case I64_LSHR:
        return new FunctorType(i64, i64, i64);
      case I64_GE:
      case I64_GT:
      case I64_LE:
      case I64_LT:
        return new FunctorType(i64, i64, bool);
      case I64_SCMP:
      case I64_UCMP:
        return new FunctorType(i64, i64, cmp);
      case IS_SAT:
      case IS_VALID:
        return new FunctorType(smt(bool), bool);
      case IS_SET_SAT:
        return new FunctorType(opaqueSet(smt(bool)), option(i32), option(bool));
      case IS_SAT_OPT:
        return new FunctorType(list(smt(bool)), option(i32), option(bool));
      case PRINT:
        return new FunctorType(a, bool);
      case QUERY_MODEL:
        return new FunctorType(sym(a), model, option(a));
      case STRING_CONCAT:
        return new FunctorType(string, string, string);
      case STRING_CMP:
        return new FunctorType(string, string, cmp);
      case STRING_MATCHES:
        return new FunctorType(string, string, bool);
      case TO_STRING:
        return new FunctorType(a, string);
      case STRING_STARTS_WITH:
        return new FunctorType(string, string, bool);
      case STRING_TO_LIST:
        return new FunctorType(string, list(i32));
      case LIST_TO_STRING:
        return new FunctorType(list(i32), string);
      case CHAR_AT:
        return new FunctorType(string, i32, option(i32));
      case SUBSTRING:
        return new FunctorType(string, i32, i32, option(string));
      case STRING_LENGTH:
        return new FunctorType(string, i32);
      case fp32ToFp64:
        return new FunctorType(fp32, fp64);
      case fp32ToI32:
        return new FunctorType(fp32, i32);
      case fp32ToI64:
        return new FunctorType(fp32, i64);
      case fp64ToFp32:
        return new FunctorType(fp64, fp32);
      case fp64ToI32:
        return new FunctorType(fp64, i32);
      case fp64ToI64:
        return new FunctorType(fp64, i64);
      case i32ToFp32:
        return new FunctorType(i32, fp32);
      case i32ToFp64:
        return new FunctorType(i32, fp64);
      case i32ToI64:
        return new FunctorType(i32, i64);
      case i64ToFp32:
        return new FunctorType(i64, fp32);
      case i64ToFp64:
        return new FunctorType(i64, fp64);
      case i64ToI32:
        return new FunctorType(i64, i32);
      case stringToI32:
        return new FunctorType(string, option(i32));
      case stringToI64:
        return new FunctorType(string, option(i64));
      case OPAQUE_SET_CHOOSE:
        return new FunctorType(opaqueSet(a), option(pair(a, opaqueSet(a))));
      case OPAQUE_SET_DIFF:
        return new FunctorType(opaqueSet(a), opaqueSet(a), opaqueSet(a));
      case OPAQUE_SET_EMPTY:
        return new FunctorType(opaqueSet(a));
      case OPAQUE_SET_PLUS:
        return new FunctorType(a, opaqueSet(a), opaqueSet(a));
      case OPAQUE_SET_MINUS:
        return new FunctorType(a, opaqueSet(a), opaqueSet(a));
      case OPAQUE_SET_UNION:
        return new FunctorType(opaqueSet(a), opaqueSet(a), opaqueSet(a));
      case OPAQUE_SET_SIZE:
        return new FunctorType(opaqueSet(a), i32);
      case OPAQUE_SET_MEMBER:
        return new FunctorType(a, opaqueSet(a), bool);
      case OPAQUE_SET_SINGLETON:
        return new FunctorType(a, opaqueSet(a));
      case OPAQUE_SET_SUBSET:
        return new FunctorType(opaqueSet(a), opaqueSet(a), bool);
      case OPAQUE_SET_FROM_LIST:
        return new FunctorType(list(a), opaqueSet(a));
    }
    throw new AssertionError("impossible");
  }

  @Override
  public String toString() {
    return name;
  }
}
