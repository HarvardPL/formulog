package edu.harvard.seas.pl.formulog.db;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.validating.ast.BindingType;

public class SortedIndexedFactDb implements IndexedFactDb {

	private final Map<RelationSymbol, List<IndexedFactSet>> indices;
	private final Map<RelationSymbol, IndexedFactSet> masterIndex;

	private SortedIndexedFactDb(Map<RelationSymbol, List<IndexedFactSet>> indices,
			Map<RelationSymbol, IndexedFactSet> masterIndex) {
		this.indices = indices;
		this.masterIndex = masterIndex;
	}

	@Override
	public Set<RelationSymbol> getSymbols() {
		return Collections.unmodifiableSet(masterIndex.keySet());
	}

	@Override
	public Iterable<Term[]> getAll(RelationSymbol sym) {
		return masterIndex.get(sym).getAll();
	}

	@Override
	public boolean isEmpty(RelationSymbol sym) {
		return masterIndex.get(sym).isEmpty();
	}

	@Override
	public int countDistinct(RelationSymbol sym) {
		return masterIndex.get(sym).count();
	}

	@Override
	public int numIndices(RelationSymbol sym) {
		return indices.get(sym).size();
	}

	@Override
	public int countDuplicates(RelationSymbol sym) {
		int count = 0;
		for (IndexedFactSet idx : indices.get(sym)) {
			count += idx.count();
		}
		return count;
	}

	@Override
	public Iterable<Term[]> get(RelationSymbol sym, Term[] key, int index) {
		return indices.get(sym).get(index).lookup(key);
	}

	@Override
	public void add(RelationSymbol sym, Term[] tup) {
		assert allNormal(tup);
		IndexedFactSet master = masterIndex.get(sym);
		if (master.add(tup)) {
			for (IndexedFactSet idx : indices.get(sym)) {
				if (!idx.equals(master)) {
					idx.add(tup);
				}
			}
		}
	}

	@Override
	public void addAll(RelationSymbol sym, Iterable<Term[]> tups) {
		IndexedFactSet master = masterIndex.get(sym);
		if (master.addAll(tups)) {
			for (IndexedFactSet idx : indices.get(sym)) {
				if (!idx.equals(master)) {
					idx.addAll(tups);
				}
			}
		}
	}

	private boolean allNormal(Term[] args) {
		for (Term arg : args) {
			if (!arg.isGround() || arg.containsFunctionCall()) {
				return false;
			}
		}
		return true;
	}

	private void forEachIndex(Consumer<IndexedFactSet> f) {
		for (Iterable<IndexedFactSet> idxs : indices.values()) {
			for (IndexedFactSet idx : idxs) {
				f.accept(idx);
			}
		}
	}

	@Override
	public boolean hasFact(RelationSymbol sym, Term[] args) {
		assert allGround(args);
		return masterIndex.get(sym).contains(args);
	}

	private boolean allGround(Term[] args) {
		for (Term arg : args) {
			if (!arg.isGround()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public void clear() {
		forEachIndex(IndexedFactSet::clear);
	}

	@Override
	public String toString() {
		String s = "{\n";
		for (RelationSymbol sym : masterIndex.keySet()) {
			s += "\t" + sym + " = {\n";
			for (IndexedFactSet idx : indices.get(sym)) {
				s += idx.toString() + "\n";
			}
			s += "\t}\n";
		}
		return s + "}";
	}

	public static class SortedIndexedFactDbBuilder implements IndexedFactDbBuilder<SortedIndexedFactDb> {

		private final Map<RelationSymbol, Integer> counts = new HashMap<>();
		private final Map<RelationSymbol, Map<BindingTypeArrayWrapper, Integer>> pats = new LinkedHashMap<>();

		public SortedIndexedFactDbBuilder(Set<RelationSymbol> allSyms) {
			List<RelationSymbol> sortedSyms = allSyms.stream().sorted(SymbolComparator.INSTANCE)
					.collect(Collectors.toList());
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
			Map<RelationSymbol, List<IndexedFactSet>> indices = new HashMap<>();
			Map<RelationSymbol, IndexedFactSet> masterIndex = new HashMap<>();
			for (Map.Entry<RelationSymbol, Map<BindingTypeArrayWrapper, Integer>> e : pats.entrySet()) {
				RelationSymbol sym = e.getKey();
				List<IndexedFactSet> idxs = new ArrayList<>();
				List<Map.Entry<BindingTypeArrayWrapper, Integer>> sorted = e.getValue().entrySet().stream().sorted(cmp)
						.collect(Collectors.toList());
				for (Map.Entry<BindingTypeArrayWrapper, Integer> e2 : sorted) {
					IndexedFactSet idx = IndexedFactSet.make(e2.getKey().getArr());
					idxs.add(idx);
					if (!idx.isProjected()) {
						masterIndex.putIfAbsent(sym, idx);
					}
				}
				if (!masterIndex.containsKey(sym)) {
					BindingType[] pat = new BindingType[sym.getArity()];
					for (int i = 0; i < pat.length; ++i) {
						pat[i] = BindingType.FREE;
					}
					IndexedFactSet master = IndexedFactSet.make(pat);
					masterIndex.put(sym, master);
					idxs.add(master);
				}
				indices.put(sym, idxs);
			}
			List<RelationSymbol> sortedSyms = masterIndex.keySet().stream().sorted(SymbolComparator.INSTANCE)
					.collect(Collectors.toList());
			HashMap<RelationSymbol, IndexedFactSet> sorted = new LinkedHashMap<>();
			for (RelationSymbol sym : sortedSyms) {
				sorted.put(sym, masterIndex.get(sym));
			}
			return new SortedIndexedFactDb(indices, sorted);
		}

		private static final Comparator<Map.Entry<BindingTypeArrayWrapper, Integer>> cmp = new Comparator<Map.Entry<BindingTypeArrayWrapper, Integer>>() {

			@Override
			public int compare(Entry<BindingTypeArrayWrapper, Integer> o1, Entry<BindingTypeArrayWrapper, Integer> o2) {
				return Integer.compare(o1.getValue(), o2.getValue());
			}

		};

	}

	private static class IndexedFactSet {

		private final BindingType[] pat;
		private final NavigableSet<Term[]> s;
		private final AtomicInteger cnt = new AtomicInteger();

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
			int[] a = new int[order.size()];
			for (int i = 0; i < a.length; ++i) {
				a[i] = order.get(i);
			}
			Comparator<Term[]> cmp = new ArrayComparator<>(a, Terms.comparator);
			return new IndexedFactSet(pat, new ConcurrentSkipListSet<>(cmp));
		}

		public SortedSet<Term[]> getAll() {
			return s;
		}

		public boolean isProjected() {
			for (BindingType b : pat) {
				if (b.equals(BindingType.IGNORED)) {
					return true;
				}
			}
			return false;
		}

		public void clear() {
			s.clear();
		}

		public boolean isEmpty() {
			return s.isEmpty();
		}

		private IndexedFactSet(BindingType[] pat, NavigableSet<Term[]> s) {
			this.pat = pat;
			this.s = s;
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

		public Iterable<Term[]> lookup(Term[] tup) {
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
			str += Arrays.toString(pat);
			for (Term[] tup : s) {
				str += "\n\t";
				str += Arrays.toString(tup);
			}
			return str + "\n]";
		}

	}

	private static class ArrayComparator<T> implements Comparator<T[]> {

		private final int[] pat;
		private final Comparator<T> cmp;

		public ArrayComparator(int[] pat, Comparator<T> cmp) {
			this.pat = pat;
			this.cmp = cmp;
		}

		@Override
		public int compare(T[] o1, T[] o2) {
			for (int i = 0; i < pat.length; i++) {
				int j = pat[i];
				int c = cmp.compare(o1[j], o2[j]);
				if (c != 0) {
					return c;
				}
			}
			return 0;
		}

	}

	public static class BindingTypeArrayWrapper {
		private final BindingType[] arr;

		public BindingTypeArrayWrapper(BindingType[] arr) {
			this.arr = arr;
		}

		public BindingType[] getArr() {
			return arr;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + Arrays.hashCode(arr);
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			BindingTypeArrayWrapper other = (BindingTypeArrayWrapper) obj;
			if (!Arrays.equals(arr, other.arr))
				return false;
			return true;
		}

	}

}
