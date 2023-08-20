package edu.harvard.seas.pl.formulog.ast;

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

import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;
import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.pcollections.HashPMap;
import org.pcollections.IntTreePMap;
import org.pcollections.MapPSet;
import org.pcollections.PSet;

public class OpaqueSet extends AbstractTerm implements Primitive<Set<Term>> {

  private final PSet<Term> s;

  private OpaqueSet(PSet<Term> s) {
    this.s = s;
  }

  private static final OpaqueSet empty;

  private static final Map<PSet<Term>, OpaqueSet> memo = new ConcurrentHashMap<>();

  static {
    PSet<Term> mt = MapPSet.from(HashPMap.empty(IntTreePMap.empty()));
    empty = make(mt);
  }

  public static OpaqueSet empty() {
    return empty;
  }

  public static OpaqueSet singleton(Term t) {
    return empty.plus(t);
  }

  public static OpaqueSet fromCollection(Collection<Term> c) {
    PSet<Term> s = MapPSet.from(HashPMap.empty(IntTreePMap.empty()));
    for (Term t : c) {
      s = s.plus(t);
    }
    return make(s);
  }

  private static OpaqueSet make(PSet<Term> s) {
    return Util.lookupOrCreate(memo, s, () -> new OpaqueSet(s));
  }

  public Collection<Term> getCollection() {
    return s;
  }

  public boolean member(Term t) {
    return s.contains(t);
  }

  public OpaqueSet plus(Term t) {
    return make(s.plus(t));
  }

  public OpaqueSet minus(Term t) {
    return make(s.minus(t));
  }

  public OpaqueSet union(OpaqueSet other) {
    return make(s.plusAll(other.s));
  }

  public OpaqueSet diff(OpaqueSet other) {
    return make(s.minusAll(other.s));
  }

  public int size() {
    return s.size();
  }

  public boolean isEmpty() {
    return s.isEmpty();
  }

  public Pair<Term, OpaqueSet> choose() {
    if (isEmpty()) {
      return null;
    }
    Term t = s.iterator().next();
    return new Pair<>(t, make(s.minus(t)));
  }

  public boolean containsAll(OpaqueSet other) {
    return s.containsAll(other.s);
  }

  @Override
  public Set<Term> getVal() {
    return s;
  }

  @Override
  public Type getType() {
    return BuiltInTypes.opaqueSet(BuiltInTypes.a);
  }

  @Override
  public String toString() {
    String str = s.toString();
    return "{" + str.substring(1, str.length() - 1) + "}";
  }
}
