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
package edu.harvard.seas.pl.formulog.parsing;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;

public class Identifier {

  private final Object val;

  private Identifier(Object val) {
    this.val = val;
  }

  public static Identifier make(Var var) {
    return new Identifier(var);
  }

  public static Identifier make(FunctionSymbol sym) {
    return new Identifier(sym);
  }

  public boolean isFunctionSymbol() {
    return val instanceof FunctionSymbol;
  }

  public boolean isVar() {
    return val instanceof Var;
  }

  public FunctionSymbol asFunctionSymbol() {
    return (FunctionSymbol) val;
  }

  public Var asVar() {
    return (Var) val;
  }
}
