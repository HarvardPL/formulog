package edu.harvard.seas.pl.formulog.util;

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

public class Triple<S, T, U> {

  public final S first;
  public final T second;
  public final U third;

  public Triple(S first, T second, U third) {
    this.first = first;
    this.second = second;
    this.third = third;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((first == null) ? 0 : first.hashCode());
    result = prime * result + ((second == null) ? 0 : second.hashCode());
    result = prime * result + ((third == null) ? 0 : third.hashCode());
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    @SuppressWarnings("rawtypes")
    Triple other = (Triple) obj;
    if (first == null) {
      if (other.first != null) return false;
    } else if (!first.equals(other.first)) return false;
    if (second == null) {
      if (other.second != null) return false;
    } else if (!second.equals(other.second)) return false;
    if (third == null) {
      if (other.third != null) return false;
    } else if (!third.equals(other.third)) return false;
    return true;
  }

  @Override
  public String toString() {
    return "< " + first + " , " + second + " , " + third + " >";
  }
}
