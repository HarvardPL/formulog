/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2022-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.Set;

public class SInfixBinaryOpAtom implements SLit {

  private final STerm lhs;
  private final String op;
  private final STerm rhs;

  public SInfixBinaryOpAtom(STerm lhs_, String op_, STerm rhs_) {
    lhs = lhs_;
    op = op_;
    rhs = rhs_;
  }

  @Override
  public String toString() {
    return lhs + " " + op + " " + rhs;
  }

  @Override
  public void varSet(Set<SVar> vars) {
    lhs.varSet(vars);
    rhs.varSet(vars);
  }
}
