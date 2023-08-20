package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

import java.util.List;
import java.util.Set;

public class SAtom implements SLit {

  private final String pred;
  private final List<STerm> args;
  private final boolean isNegated;

  public SAtom(String symbol, List<STerm> args, boolean isNegated) {
    pred = symbol;
    this.args = args;
    this.isNegated = isNegated;
  }

  public String getSymbol() {
    return pred;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    if (isNegated) {
      sb.append("!");
    }
    sb.append(pred);
    sb.append("(");
    for (int i = 0; i < args.size(); ++i) {
      sb.append(args.get(i));
      if (i < args.size() - 1) {
        sb.append(", ");
      }
    }
    sb.append(")");
    return sb.toString();
  }

  @Override
  public void varSet(Set<SVar> vars) {
    for (var t : args) {
      t.varSet(vars);
    }
  }
}
