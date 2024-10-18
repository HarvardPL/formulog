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
package edu.harvard.seas.pl.formulog.db;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NavigableSet;
import java.util.Set;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

public class SortedIndexedFactDb implements IndexedFactDb {

  private final Map<RelationSymbol, Pair<IndexedFactSet, BindingType[]>[]> indices;
  private final Map<RelationSymbol, Pair<IndexedFactSet, BindingType[]>> masterIndex;

  private final Map<RelationSymbol, Set<HashedTuple>> hashFilter = new HashMap<>();
  private final ThreadLocal<HashedTuple> hashKey = ThreadLocal.withInitial(HashedTuple::new);

  private SortedIndexedFactDb(
      Map<RelationSymbol, Pair<IndexedFactSet, BindingType[]>[]> indices,
      Map<RelationSymbol, Pair<IndexedFactSet, BindingType[]>> masterIndex) {
    this.indices = indices;
    this.masterIndex = masterIndex;
    for (var sym : indices.keySet()) {
      hashFilter.put(sym, Util.concurrentSet());
    }
  }

  private static class HashedTuple {
    public Term[] tup;

    @Override
    public int hashCode() {
      return Arrays.hashCode(tup);
    }

    @Override
    public boolean equals(Object other) {
      if (other instanceof HashedTuple) {
        return Arrays.equals(tup, ((HashedTuple) other).tup);
      }
      return false;
    }
  }

  @Override
  public Set<RelationSymbol> getSymbols() {
    return Collections.unmodifiableSet(masterIndex.keySet());
  }

  @Override
  public Iterable<Term[]> getAll(RelationSymbol sym) {
    return masterIndex.get(sym).fst().getAll();
  }

  @Override
  public boolean isEmpty(RelationSymbol sym) {
    return masterIndex.get(sym).fst().isEmpty();
  }

  @Override
  public int countDistinct(RelationSymbol sym) {
    return masterIndex.get(sym).fst().count();
  }

  @Override
  public int countDuplicates(RelationSymbol sym) {
    int count = 0;
    for (IndexedFactSet idx : getUniqueIndices(sym)) {
      count += idx.count();
    }
    return count;
  }

  private Set<IndexedFactSet> getUniqueIndices(RelationSymbol sym) {
    Set<IndexedFactSet> s = new HashSet<>();
    for (Pair<IndexedFactSet, ?> e : indices.get(sym)) {
      s.add(e.fst());
    }
    return s;
  }

  @Override
  public Iterable<Term[]> get(RelationSymbol sym, Term[] key, int index) {
    Pair<IndexedFactSet, BindingType[]> p = indices.get(sym)[index];
    return p.fst().lookup(key, p.snd());
  }

  private boolean hashFilterAdd(RelationSymbol sym, Term[] tup) {
    var key = hashKey.get();
    key.tup = tup;
    if (hashFilter.get(sym).add(key)) {
      hashKey.set(new HashedTuple());
      return true;
    }
    key.tup = null;
    return false;
  }

  private boolean hashFilterContains(RelationSymbol sym, Term[] tup) {
    var key = hashKey.get();
    key.tup = tup;
    var r = hashFilter.get(sym).contains(key);
    key.tup = null;
    return r;
  }

  @Override
  public boolean add(RelationSymbol sym, Term[] tup) {
    assert allNormal(tup);
    if (Configuration.useHashDbFilter && !hashFilterAdd(sym, tup)) {
      return false;
    }
    IndexedFactSet master = masterIndex.get(sym).fst();
    if (master.add(tup)) {
      for (Pair<IndexedFactSet, ?> p : indices.get(sym)) {
        IndexedFactSet idx = p.fst();
        if (!idx.equals(master)) {
          idx.add(tup);
        }
      }
      return true;
    }
    return false;
  }

  @Override
  public boolean addAll(RelationSymbol sym, Iterable<Term[]> tups) {
    if (Configuration.useHashDbFilter) {
      ArrayList<Term[]> l = new ArrayList<>();
      for (var tup : tups) {
        if (hashFilterAdd(sym, tup)) {
          l.add(tup);
        }
      }
      tups = l;
    }
    IndexedFactSet master = masterIndex.get(sym).fst();
    if (master.addAll(tups)) {
      for (Pair<IndexedFactSet, ?> p : indices.get(sym)) {
        IndexedFactSet idx = p.fst();
        if (!idx.equals(master)) {
          idx.addAll(tups);
        }
      }
      return true;
    }
    return false;
  }

  private boolean allNormal(Term[] args) {
    for (Term arg : args) {
      if (!arg.isGround() || arg.containsUnevaluatedTerm()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean hasFact(RelationSymbol sym, Term[] args) {
    assert allNormal(args);
    if (Configuration.useHashDbFilter) {
      return hashFilterContains(sym, args);
    }
    return masterIndex.get(sym).fst().contains(args);
  }

  @Override
  public void clear() {
    for (var s : hashFilter.values()) {
      s.clear();
    }
    for (Pair<IndexedFactSet, BindingType[]>[] idxs : indices.values()) {
      for (Pair<IndexedFactSet, ?> p : idxs) {
        p.fst().clear();
      }
    }
  }

  @Override
  public String toString() {
    String s = "{\n";
    for (RelationSymbol sym : masterIndex.keySet()) {
      s += "\t" + sym + " = {\n";
      for (Pair<IndexedFactSet, BindingType[]> p : indices.get(sym)) {
        s += "\t" + Arrays.toString(p.snd()) + "\n";
        s += p.fst().toString() + "\n";
      }
      s += "\t}\n";
    }
    return s + "}";
  }

  public String toSimplifiedString() {
    String s = "{\n";
    for (RelationSymbol sym : masterIndex.keySet()) {
      Pair<IndexedFactSet, BindingType[]> p = masterIndex.get(sym);
      IndexedFactSet idx = p.fst();
      if (!idx.isEmpty()) {
        s += "\t" + sym + " = {\n";
        s += "\t" + Arrays.toString(p.snd()) + "\n";
        s += idx.toString() + "\n";
        s += "\t}\n";
      }
    }
    return s + "}";
  }

  @Override
  public int numIndices(RelationSymbol sym) {
    if (!indices.containsKey(sym)) {
      throw new IllegalArgumentException("Unrecognized symbol: " + sym);
    }
    return getUniqueIndices(sym).size();
  }

  public IndexInfo getIndexInfo(RelationSymbol sym, int idx) {
    if (idx < 0 || idx > numIndices(sym)) {
      throw new IllegalArgumentException("Unrecognized index for symbol " + sym + ": " + idx);
    }
    Pair<IndexedFactSet, BindingType[]> p = indices.get(sym)[idx];
    IndexedFactSet index = p.fst();
    return new IndexInfo(index.getId(), index.comparatorOrder, p.snd());
  }

  public int getMasterIndex(RelationSymbol sym) {
    if (!indices.containsKey(sym)) {
      throw new IllegalArgumentException("Unrecognized symbol: " + sym);
    }
    int i = 0;
    IndexedFactSet master = masterIndex.get(sym).fst();
    for (Pair<IndexedFactSet, ?> p : indices.get(sym)) {
      if (p.fst().equals(master)) {
        break;
      }
      i++;
    }
    return i;
  }

  public static class SortedIndexedFactDbBuilder
      implements IndexedFactDbBuilder<SortedIndexedFactDb> {

    private final Map<RelationSymbol, Integer> counts = new HashMap<>();
    private final Map<RelationSymbol, Map<BindingTypeArrayWrapper, Integer>> pats =
        new LinkedHashMap<>();
    private final Map<RelationSymbol, Pair<IndexedFactSet, BindingType[]>> masterIndex =
        new HashMap<>();

    public SortedIndexedFactDbBuilder(Set<RelationSymbol> allSyms) {
      List<RelationSymbol> sortedSyms =
          allSyms.stream().sorted(SymbolComparator.INSTANCE).collect(Collectors.toList());
      for (RelationSymbol sym : sortedSyms) {
        pats.put(sym, new HashMap<>());
        counts.put(sym, 0);
      }
    }

    @Override
    public synchronized int makeIndex(RelationSymbol sym, BindingType[] pat) {
      assert sym.getArity() == pat.length;
      Map<BindingTypeArrayWrapper, Integer> m = pats.get(sym);
      BindingTypeArrayWrapper key = new BindingTypeArrayWrapper(pat);
      assert m != null : "Symbol not registered with DB: " + sym;
      Integer idx = m.get(key);
      if (idx == null) {
        idx = counts.get(sym);
        counts.put(sym, idx + 1);
        m.put(key, idx);
      }
      return idx;
    }

    @Override
    public SortedIndexedFactDb build() {
      Map<RelationSymbol, Pair<IndexedFactSet, BindingType[]>[]> indices = new HashMap<>();
      for (Map.Entry<RelationSymbol, Map<BindingTypeArrayWrapper, Integer>> e : pats.entrySet()) {
        RelationSymbol sym = e.getKey();
        indices.put(sym, mkIndices(sym, e.getValue()));
      }

      List<RelationSymbol> sortedSyms =
          counts.keySet().stream().sorted(SymbolComparator.INSTANCE).collect(Collectors.toList());
      HashMap<RelationSymbol, Pair<IndexedFactSet, BindingType[]>> sorted = new LinkedHashMap<>();
      for (RelationSymbol sym : sortedSyms) {
        sorted.put(sym, masterIndex.get(sym));
      }
      return new SortedIndexedFactDb(indices, sorted);
    }

    @SuppressWarnings("unchecked")
    private Pair<IndexedFactSet, BindingType[]>[] mkIndices(
        RelationSymbol sym, Map<BindingTypeArrayWrapper, Integer> m) {
      List<Pair<IndexedFactSet, BindingType[]>> indices;
      if (Configuration.minIndex) {
        indices = mkMinIndices(sym, m);
      } else {
        indices = mkNaiveIndices(sym, m);
      }
      boolean ok = false;
      for (Pair<IndexedFactSet, BindingType[]> p : indices) {
        IndexedFactSet idx = p.fst();
        if (idx.comparatorLength() == sym.getArity()) {
          masterIndex.put(sym, new Pair<>(idx, p.snd()));
          ok = true;
          break;
        }
      }
      if (!ok) {
        BindingType[] pat = new BindingType[sym.getArity()];
        for (int i = 0; i < pat.length; ++i) {
          pat[i] = BindingType.FREE;
        }
        IndexedFactSet master = IndexedFactSet.make(pat);
        Pair<IndexedFactSet, BindingType[]> p = new Pair<>(master, pat);
        masterIndex.put(sym, p);
        indices.add(p);
      }
      assert indicesWellFormed(indices) : "Bad index created for relation: " + sym;
      return indices.toArray(new Pair[0]);
    }

    private static boolean indicesWellFormed(
        Iterable<Pair<IndexedFactSet, BindingType[]>> indices) {
      boolean ok = true;
      for (Pair<IndexedFactSet, BindingType[]> p : indices) {
        ok &= p.fst().comparatorLength() == countNumNotIgnored(p.snd());
      }
      return ok;
    }

    private static int countNumNotIgnored(BindingType[] pat) {
      int i = 0;
      for (BindingType b : pat) {
        if (!b.isIgnored()) {
          i++;
        }
      }
      return i;
    }

    private List<Pair<IndexedFactSet, BindingType[]>> mkNaiveIndices(
        RelationSymbol sym, Map<BindingTypeArrayWrapper, Integer> m) {
      List<Pair<IndexedFactSet, BindingType[]>> idxs = new ArrayList<>();
      List<Map.Entry<BindingTypeArrayWrapper, Integer>> sorted =
          m.entrySet().stream().sorted(cmp).collect(Collectors.toList());
      for (Map.Entry<BindingTypeArrayWrapper, Integer> e : sorted) {
        BindingType[] pat = e.getKey().getArr();
        IndexedFactSet idx = IndexedFactSet.make(pat);
        idxs.add(new Pair<>(idx, pat));
      }
      return idxs;
    }

    private List<Pair<IndexedFactSet, BindingType[]>> mkMinIndices(
        RelationSymbol sym, Map<BindingTypeArrayWrapper, Integer> m) {
      List<Pair<IndexedFactSet, BindingType[]>> indices = new ArrayList<>(m.size());
      for (int i = 0; i < m.size(); ++i) {
        indices.add(null);
      }
      for (Map.Entry<Set<Integer>, Set<Pair<Integer, BindingType[]>>> e1 :
          partitionByIgnoredPositions(m).entrySet()) {
        for (Map.Entry<Integer, Pair<IndexedFactSet, BindingType[]>> e2 :
            mkMinIndices(sym, e1.getKey(), e1.getValue()).entrySet()) {
          assert indices.get(e2.getKey()) == null;
          indices.set(e2.getKey(), e2.getValue());
        }
      }
      return indices;
    }

    private Map<Integer, Pair<IndexedFactSet, BindingType[]>> mkMinIndices(
        RelationSymbol sym, Set<Integer> ignored, Set<Pair<Integer, BindingType[]>> s) {
      Map<Integer, Set<Integer>> searchByNum = new HashMap<>();
      Map<Integer, BindingType[]> bindingsByNum = new HashMap<>();
      Set<Set<Integer>> searches = new HashSet<>();
      for (Pair<Integer, BindingType[]> p : s) {
        Set<Integer> search = new HashSet<>();
        BindingType[] pat = p.snd();
        for (int i = 0; i < pat.length; ++i) {
          if (pat[i].isBound()) {
            search.add(i);
          }
        }
        searches.add(search);
        int i = p.fst();
        searchByNum.put(i, search);
        bindingsByNum.put(i, pat);
      }
      Set<Integer> domain = mkDomain(sym.getArity(), ignored);
      Map<Set<Integer>, Iterable<Integer>> indexBySearch = MinIndex.compute(domain, searches);
      Map<Iterable<Integer>, IndexedFactSet> factSetByIndex = new HashMap<>();
      for (Iterable<Integer> idx : indexBySearch.values()) {
        List<Integer> order = new ArrayList<>();
        for (int i : idx) {
          order.add(i);
        }
        factSetByIndex.put(idx, IndexedFactSet.make(order));
      }
      Map<Integer, Pair<IndexedFactSet, BindingType[]>> indices = new HashMap<>();
      for (int i : searchByNum.keySet()) {
        Set<Integer> search = searchByNum.get(i);
        BindingType[] pat = bindingsByNum.get(i);
        Iterable<Integer> idx = indexBySearch.get(search);
        indices.put(i, new Pair<>(factSetByIndex.get(idx), pat));
      }
      return indices;
    }

    private static Set<Integer> mkDomain(int arity, Set<Integer> ignored) {
      Set<Integer> s = new HashSet<>();
      for (int i = 0; i < arity; ++i) {
        if (!ignored.contains(i)) {
          s.add(i);
        }
      }
      return s;
    }

    private static Map<Set<Integer>, Set<Pair<Integer, BindingType[]>>> partitionByIgnoredPositions(
        Map<BindingTypeArrayWrapper, Integer> m) {
      Map<Set<Integer>, Set<Pair<Integer, BindingType[]>>> byIgnoredPos = new HashMap<>();
      for (Map.Entry<BindingTypeArrayWrapper, Integer> e : m.entrySet()) {
        BindingType[] pat = e.getKey().getArr();
        Set<Integer> ignored = findIgnoredPositions(pat);
        Pair<Integer, BindingType[]> p = new Pair<>(e.getValue(), pat);
        Util.lookupOrCreate(byIgnoredPos, ignored, () -> new HashSet<>()).add(p);
      }
      return byIgnoredPos;
    }

    private static Set<Integer> findIgnoredPositions(BindingType[] pat) {
      Set<Integer> ignored = new HashSet<>();
      for (int i = 0; i < pat.length; ++i) {
        if (pat[i].isIgnored()) {
          ignored.add(i);
        }
      }
      return ignored;
    }

    private static final Comparator<Map.Entry<BindingTypeArrayWrapper, Integer>> cmp =
        new Comparator<Map.Entry<BindingTypeArrayWrapper, Integer>>() {

          @Override
          public int compare(
              Entry<BindingTypeArrayWrapper, Integer> o1,
              Entry<BindingTypeArrayWrapper, Integer> o2) {
            return Integer.compare(o1.getValue(), o2.getValue());
          }
        };
  }

  private static class IndexedFactSet {

    private static final AtomicInteger idCnt = new AtomicInteger();
    private final int id;
    private final NavigableSet<Term[]> s;
    private final AtomicInteger cnt = new AtomicInteger();
    private final List<Integer> comparatorOrder;

    private static final TupleComparatorGenerator gen = new TupleComparatorGenerator();

    public static IndexedFactSet make(BindingType[] pat) {
      List<Integer> order = new ArrayList<>();
      for (int i = 0; i < pat.length; ++i) {
        if (pat[i].isBound()) {
          order.add(i);
        }
      }
      for (int i = 0; i < pat.length; ++i) {
        if (pat[i].isFree()) {
          order.add(i);
        }
      }
      return make(order);
    }

    private static IndexedFactSet make(List<Integer> order) {
      int[] a = new int[order.size()];
      for (int i = 0; i < a.length; ++i) {
        a[i] = order.get(i);
      }
      Comparator<Term[]> cmp;
      if (Configuration.genComparators) {
        try {
          cmp = gen.generate(a);
        } catch (InstantiationException
            | IllegalAccessException
            | IllegalArgumentException
            | InvocationTargetException
            | NoSuchMethodException
            | SecurityException e) {
          throw new AssertionError(e);
        }
      } else {
        cmp = new TermArrayComparator(a);
      }
      return new IndexedFactSet(new ConcurrentSkipListSet<>(cmp), order);
    }

    public int comparatorLength() {
      return comparatorOrder.size();
    }

    public Iterable<Term[]> getAll() {
      return s;
    }

    public void clear() {
      s.clear();
      cnt.set(0);
    }

    public boolean isEmpty() {
      return s.isEmpty();
    }

    private IndexedFactSet(NavigableSet<Term[]> s, List<Integer> comparatorOrder) {
      this.s = s;
      this.comparatorOrder = comparatorOrder;
      this.id = idCnt.getAndIncrement();
    }

    public int getId() {
      return id;
    }

    public boolean add(Term[] arr) {
      boolean modified = s.add(arr);
      if (modified) {
        cnt.incrementAndGet();
      }
      return modified;
    }

    public boolean addAll(Iterable<Term[]> tups) {
      boolean modified = false;
      int delta = 0;
      for (Term[] tup : tups) {
        if (s.add(tup)) {
          modified = true;
          delta++;
        }
      }
      if (modified) {
        cnt.addAndGet(delta);
      }
      return modified;
    }

    public int count() {
      return cnt.get();
    }

    public Iterable<Term[]> lookup(Term[] tup, BindingType[] pat) {
      Term[] lower = new Term[tup.length];
      Term[] upper = new Term[tup.length];
      for (int i = 0; i < tup.length; ++i) {
        if (pat[i].isBound()) {
          lower[i] = tup[i];
          upper[i] = tup[i];
        } else {
          lower[i] = Terms.minTerm;
          upper[i] = Terms.maxTerm;
        }
      }
      return s.subSet(lower, true, upper, true);
    }

    public boolean contains(Term[] tup) {
      return s.contains(tup);
    }

    @Override
    public String toString() {
      String str = "[\n\t";
      str += "\t#" + id + " " + comparatorOrder + "\n";
      for (Term[] tup : s) {
        str += "\n\t";
        str += Arrays.toString(tup);
      }
      return str + "\n]";
    }
  }

  private static class TermArrayComparator implements Comparator<Term[]> {

    private final int[] pat;

    public TermArrayComparator(int[] pat) {
      this.pat = pat;
    }

    @Override
    public int compare(Term[] o1, Term[] o2) {
      for (int i = 0; i < pat.length; i++) {
        int j = pat[i];
        int x = o1[j].getId();
        int y = o2[j].getId();
        if (x < y) {
          return -1;
        } else if (x > y) {
          return 1;
        }
      }
      return 0;
    }
  }

  public class IndexInfo {

    private final int indexId;
    private final List<Integer> comparatorOrder;
    private final BindingType[] pat;

    private IndexInfo(int indexId, List<Integer> comparatorOrder, BindingType[] pat) {
      this.indexId = indexId;
      this.comparatorOrder = Collections.unmodifiableList(comparatorOrder);
      this.pat = pat;
    }

    public List<Integer> getComparatorOrder() {
      return comparatorOrder;
    }

    public BindingType[] getPattern() {
      return pat;
    }

    public int getIndexId() {
      return indexId;
    }
  }
}
