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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.ast.BindingType;

public class SortedIndexedFactDb implements IndexedFactDb {

	private final Map<RelationSymbol, SortedSet<Term[]>> all;
	private final IndexedFactSet[] indices;
	private final Map<RelationSymbol, Iterable<Integer>> relevantIndices;
	private final ExecutorService[] threads;
	private final AtomicInteger[] taskCounters;

	private SortedIndexedFactDb(Map<RelationSymbol, SortedSet<Term[]>> all, IndexedFactSet[] indices,
			Map<RelationSymbol, Iterable<Integer>> relevantIndices) {
		this.all = all;
		this.indices = indices;
		this.relevantIndices = relevantIndices;
		threads = new ExecutorService[indices.length];
		taskCounters = new AtomicInteger[indices.length];
		for (int i = 0; i < indices.length; ++i) {
			threads[i] = Executors.newSingleThreadExecutor();
			taskCounters[i] = new AtomicInteger();
		}
	}

	@Override
	public Set<RelationSymbol> getSymbols() {
		return all.keySet();
	}

	@Override
	public SortedSet<Term[]> getAll(RelationSymbol sym) {
		return all.get(sym);
	}

	@Override
	public View get(Term[] key, int index) {
		return indices[index].lookup(key);
	}

	@Override
	public boolean add(RelationSymbol sym, Term[] args) {
		assert allNormal(args);
		if (!all.get(sym).add(args)) {
			return false;
		}
		for (Integer idx : relevantIndices.get(sym)) {
			AtomicInteger counter = taskCounters[idx];
			counter.incrementAndGet();
			threads[idx].execute(() -> {
				indices[idx].add(args);
				if (counter.decrementAndGet() == 0) {
					synchronized (counter) {
						counter.notify();
					}
				}
			});
		}
		return true;
	}

	@Override
	public boolean addAll(RelationSymbol sym, Set<Term[]> tups) {
		boolean somethingNew = all.get(sym).addAll(tups);
		if (somethingNew) {
			for (Integer idx : relevantIndices.get(sym)) {
				AtomicInteger counter = taskCounters[idx];
				counter.incrementAndGet();
				threads[idx].execute(() -> {
					indices[idx].addAll(tups);
					if (counter.decrementAndGet() == 0) {
						synchronized (counter) {
							counter.notify();
						}
					}
				});
			}
		}
		return somethingNew;
	}

	private boolean allNormal(Term[] args) {
		for (Term arg : args) {
			if (!arg.isGround() || arg.containsFunctionCall()) {
				return false;
			}
		}
		return true;
	}

	public void synchronize() {
		for (AtomicInteger counter : taskCounters) {
			synchronized (counter) {
				while (counter.get() > 0) {
					try {
						counter.wait();
					} catch (InterruptedException e) {
						// do nothing
					}
				}
			}
		}
		for (IndexedFactSet idx : indices) {
			idx.synchronize();
		}
	}

	public void shutdown() {
		for (ExecutorService exec : threads) {
			exec.shutdown();
		}
	}

	@Override
	public boolean hasFact(RelationSymbol sym, Term[] args) {
		assert allGround(args);
		return all.get(sym).contains(args);
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
		for (Set<Term[]> s : all.values()) {
			s.clear();
		}
		for (IndexedFactSet index : indices) {
			index.clear();
		}
	}

	@Override
	public String toString() {
		String s = "{\n";
		for (RelationSymbol sym : all.keySet()) {
			s += "\t" + sym + " = {\n";
			for (Term[] args : all.get(sym)) {
				s += "\t\t" + Arrays.toString(args) + "\n";
			}
			s += "\t}\n";
		}
		return s + "}";
	}

	public static class SortedIndexedFactDbBuilder implements IndexedFactDbBuilder<SortedIndexedFactDb> {

		private int cnt = 0;
		private final Map<RelationSymbol, Map<BindingTypeArrayWrapper, Integer>> pats = new LinkedHashMap<>();

		public SortedIndexedFactDbBuilder(Set<RelationSymbol> allSyms) {
			List<RelationSymbol> sortedSyms = allSyms.stream().sorted(SymbolComparator.INSTANCE)
					.collect(Collectors.toList());
			for (RelationSymbol sym : sortedSyms) {
				pats.put(sym, new HashMap<>());
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
				idx = cnt++;
				m.put(key, idx);
			}
			return idx;
		}

		@Override
		public SortedIndexedFactDb build() {
			Map<RelationSymbol, SortedSet<Term[]>> all = new LinkedHashMap<>();
			IndexedFactSet[] indices = new IndexedFactSet[cnt];
			Map<RelationSymbol, Iterable<Integer>> relevantIndices = new HashMap<>();
			for (Map.Entry<RelationSymbol, Map<BindingTypeArrayWrapper, Integer>> e : pats.entrySet()) {
				RelationSymbol sym = e.getKey();
				int[] order = new int[sym.getArity()];
				for (int i = 0; i < order.length; ++i) {
					order[i] = i;
				}
				Comparator<Term[]> cmp = new ArrayComparator<>(order, Terms.comparator);
				all.put(sym, new ConcurrentSkipListSet<>(cmp));
				List<Integer> idxs = new ArrayList<>();
				for (Map.Entry<BindingTypeArrayWrapper, Integer> e2 : e.getValue().entrySet()) {
					int idx = e2.getValue();
					indices[idx] = IndexedFactSet.make(e2.getKey().getArr());
					idxs.add(idx);
				}
				relevantIndices.put(sym, idxs);
			}
			return new SortedIndexedFactDb(all, indices, relevantIndices);
		}

	}

	private static class IndexedFactSet {

		private final BindingType[] pat;
		private final NavigableSet<Term[]> s;

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
			return new IndexedFactSet(pat, new TreeSet<>(cmp));
		}

		public void clear() {
			s.clear();
		}

		private IndexedFactSet(BindingType[] pat, NavigableSet<Term[]> s) {
			this.pat = pat;
			this.s = s;
		}

		public synchronized void add(Term[] arr) {
			s.add(arr);
		}

		public synchronized void addAll(Set<Term[]> tups) {
			s.addAll(tups);
		}

		public synchronized void synchronize() {

		}

		public View lookup(Term[] arr) {
			Term[] lower = new Term[arr.length];
			Term[] upper = new Term[arr.length];
			for (int i = 0; i < arr.length; ++i) {
				if (pat[i].isBound()) {
					lower[i] = arr[i];
					upper[i] = arr[i];
				} else {
					lower[i] = Terms.minTerm;
					upper[i] = Terms.maxTerm;
				}
			}
			return makeView(s.subSet(lower, true, upper, true));
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

		private View makeView(NavigableSet<Term[]> set) {
			if (set.isEmpty()) {
				return emptyView;
			}
			Term[][] arr = new Term[set.size()][];
			int i = 0;
			for (Term[] tup : set) {
				arr[i] = tup;
				i++;
			}
			return new ArrayView(arr, 0, arr.length);
		}

		private static final View emptyView = new View() {

			@Override
			public Iterator<Term[]> iterator() {
				return Collections.emptyIterator();
			}

			@Override
			public int size() {
				return 0;
			}

			@Override
			public boolean isEmpty() {
				return true;
			}

			@Override
			public Pair<View, View> split() {
				return null;
			}

		};

		private class ArrayView implements View {

			private final Term[][] arr;
			private final int lower;
			private final int upper;

			public ArrayView(Term[][] arr, int lower, int upper) {
				assert lower < upper;
				this.arr = arr;
				this.lower = lower;
				this.upper = upper;
			}

			@Override
			public Iterator<Term[]> iterator() {
				return new ArrayViewIterator();
			}

			@Override
			public int size() {
				return upper - lower;
			}

			@Override
			public boolean isEmpty() {
				return false;
			}

			@Override
			public Pair<View, View> split() {
				if (size() < 2) {
					return null;
				}
				int mid = (upper - lower) / 2 + lower;
				View v1 = new ArrayView(arr, lower, mid);
				View v2 = new ArrayView(arr, mid, upper);
				return new Pair<>(v1, v2);
			}

			private class ArrayViewIterator implements Iterator<Term[]> {

				private int pos = lower;

				@Override
				public boolean hasNext() {
					return pos < upper;
				}

				@Override
				public Term[] next() {
					Term[] tup = arr[pos];
					pos++;
					return tup;
				}

			}

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
