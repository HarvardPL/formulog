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

import java.util.List;
import java.util.Set;

public class SIntList implements STerm {

  private final List<STerm> ts;

  public SIntList(List<STerm> ts_) {
    ts = ts_;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("[");
    for (int i = 0; i < ts.size(); ++i) {
      sb.append(ts.get(i));
      if (i < ts.size() - 1) {
        sb.append(", ");
      }
    }
    sb.append("]");
    return sb.toString();
  }

  @Override
  public void varSet(Set<SVar> vars) {
    for (var t : ts) {
      t.varSet(vars);
    }
  }
}
