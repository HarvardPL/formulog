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
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public enum BuiltInConstructorGetterSymbol implements ConstructorSymbol {
  CONS_1("#cons_1", list(a), smt(a)),

  CONS_2("#cons_2", list(a), smt(list(a))),

  SOME_1("#some_1", option(a), smt(a));

  private final String name;
  private final FunctorType type;

  private BuiltInConstructorGetterSymbol(String name, Type... types) {
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
  public FunctorType getCompileTimeType() {
    return type;
  }

  @Override
  public String toString() {
    return name;
  }

  @Override
  public ConstructorSymbolType getConstructorSymbolType() {
    return ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER;
  }
}
