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
package edu.harvard.seas.pl.formulog.magic;

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.WrappedRelationSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import java.util.Arrays;

class AdornedSymbol implements WrappedRelationSymbol<RelationSymbol> {

  private final RelationSymbol baseSymbol;
  private final boolean[] adornment;

  public AdornedSymbol(RelationSymbol baseSymbol, boolean[] adornment) {
    assert adornment != null;
    assert !(baseSymbol instanceof AdornedSymbol);
    assert baseSymbol.isIdbSymbol();
    this.baseSymbol = baseSymbol;
    this.adornment = adornment;
  }

  public boolean[] getAdornment() {
    return adornment;
  }

  @Override
  public String toString() {
    String s = getBaseSymbol() + "_";
    for (boolean b : adornment) {
      s += b ? "b" : "f";
    }
    return s;
  }

  @Override
  public boolean isIdbSymbol() {
    return baseSymbol.isIdbSymbol();
  }

  @Override
  public boolean isBottomUp() {
    return baseSymbol.isBottomUp();
  }

  @Override
  public boolean isTopDown() {
    return baseSymbol.isTopDown();
  }

  @Override
  public FunctorType getCompileTimeType() {
    return baseSymbol.getCompileTimeType();
  }

  @Override
  public int getArity() {
    return baseSymbol.getArity();
  }

  @Override
  public RelationSymbol getBaseSymbol() {
    return baseSymbol;
  }

  @Override
  public boolean isDisk() {
    return false;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + Arrays.hashCode(adornment);
    result = prime * result + ((baseSymbol == null) ? 0 : baseSymbol.hashCode());
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    AdornedSymbol other = (AdornedSymbol) obj;
    if (!Arrays.equals(adornment, other.adornment)) return false;
    if (baseSymbol == null) {
      if (other.baseSymbol != null) return false;
    } else if (!baseSymbol.equals(other.baseSymbol)) return false;
    return true;
  }
}
