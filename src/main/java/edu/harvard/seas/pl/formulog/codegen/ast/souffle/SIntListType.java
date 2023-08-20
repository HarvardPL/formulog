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

import java.util.Objects;

public class SIntListType implements SType {

  private final int arity;

  public SIntListType(int arity) {
    this.arity = arity;
  }

  public String getName() {
    return "IntList" + arity;
  }

  public String getDef() {
    StringBuilder sb = new StringBuilder();
    sb.append("[");
    for (int i = 0; i < arity; ++i) {
      sb.append("x");
      sb.append(i);
      sb.append(":number");
      if (i < arity - 1) {
        sb.append(", ");
      }
    }
    sb.append("]");
    return sb.toString();
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    SIntListType that = (SIntListType) o;
    return arity == that.arity;
  }

  @Override
  public int hashCode() {
    return Objects.hash(arity);
  }

  @Override
  public String toString() {
    return getName();
  }
}
