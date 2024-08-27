/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2019-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.symbols;

import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.cmp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public enum BuiltInConstructorTesterSymbol implements ConstructorSymbol {
  IS_CMP_LT("#is_cmp_lt", cmp, smt(bool)),

  IS_CMP_EQ("#is_cmp_eq", cmp, smt(bool)),

  IS_CMP_GT("#is_cmp_gt", cmp, smt(bool)),

  IS_NIL("#is_nil", list(a), smt(bool)),

  IS_CONS("#is_cons", list(a), smt(bool)),

  IS_NONE("#is_none", option(a), smt(bool)),

  IS_SOME("#is_some", option(a), smt(bool)),
  ;

  private final FunctorType type;
  private final String name;

  private BuiltInConstructorTesterSymbol(String name, Type... types) {
    this.name = name;
    List<Type> argTypes = new ArrayList<>(Arrays.asList(types));
    Type retType = argTypes.remove(types.length - 1);
    type = new FunctorType(argTypes, retType);
  }

  @Override
  public int getArity() {
    return 1;
  }

  @Override
  public ConstructorSymbolType getConstructorSymbolType() {
    return ConstructorSymbolType.SOLVER_CONSTRUCTOR_TESTER;
  }

  @Override
  public FunctorType getCompileTimeType() {
    return type;
  }

  @Override
  public String toString() {
    return name;
  }
}
