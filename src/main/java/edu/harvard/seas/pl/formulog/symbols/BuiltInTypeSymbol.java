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

public enum BuiltInTypeSymbol implements TypeSymbol {
  BOOL_TYPE("bool", 0),

  LIST_TYPE("list", 1),

  OPTION_TYPE("option", 1),

  CMP_TYPE("cmp", 0),

  STRING_TYPE("string", 0),

  SMT_TYPE("smt", 1),

  SYM_TYPE("sym", 1),

  ARRAY_TYPE("array", 2),

  MODEL_TYPE("model", 0),

  INT_TYPE("int", 0),

  BV("bv", 1),

  FP("fp", 2),

  OPAQUE_SET("opaque_set", 1),

  SMT_PATTERN_TYPE("smt_pattern", 0),

  SMT_WRAPPED_VAR_TYPE("smt_wrapped_var", 0),
  ;

  private final String name;
  private final int arity;

  private BuiltInTypeSymbol(String name, int arity) {
    this.name = name;
    this.arity = arity;
  }

  @Override
  public int getArity() {
    return arity;
  }

  @Override
  public TypeSymbolType getTypeSymbolType() {
    return TypeSymbolType.NORMAL_TYPE;
  }

  @Override
  public String toString() {
    return name;
  }
}
