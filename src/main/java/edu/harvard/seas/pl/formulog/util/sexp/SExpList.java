package edu.harvard.seas.pl.formulog.util.sexp;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2021 President and Fellows of Harvard College
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

public class SExpList implements SExp {

  private final List<SExp> l;

  public SExpList(List<SExp> l) {
    this.l = Collections.unmodifiableList(new ArrayList<>(l));
  }

  @Override
  public boolean isAtom() {
    return false;
  }

  @Override
  public String asAtom() {
    throw new UnsupportedOperationException();
  }

  @Override
  public List<SExp> asList() {
    return l;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    for (Iterator<SExp> it = l.iterator(); it.hasNext(); ) {
      sb.append(it.next());
      if (it.hasNext()) {
        sb.append(" ");
      }
    }
    sb.append(")");
    return sb.toString();
  }
}
