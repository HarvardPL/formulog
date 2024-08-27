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

import edu.harvard.seas.pl.formulog.types.FunctorType;

abstract class AbstractTypedSymbol extends AbstractSymbol implements TypedSymbol {

  private final FunctorType type;

  public AbstractTypedSymbol(String name, int arity, FunctorType type) {
    super(name, arity);
    this.type = type;
  }

  @Override
  public FunctorType getCompileTimeType() {
    return type;
  }
}
