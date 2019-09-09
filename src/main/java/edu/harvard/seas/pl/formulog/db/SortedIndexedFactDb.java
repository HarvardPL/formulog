package edu.harvard.seas.pl.formulog.db;

import java.util.ArrayList;
import java.util.Arrays;

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
import java.util.NavigableSet;
import java.util.Set;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.validating.ast.BindingType;

public class SortedIndexedFactDb implements IndexedFactDb {

	private final Map<RelationSymbol, Set<Term[]>> all;
	private final IndexedFactSet[] indices;
	private final Map<RelationSymbol, Iterable<Integer>> relevantIndices;

	private SortedIndexedFactDb(Map<RelationSymbol, Set<Term[]>> all, IndexedFactSet[] indices,
			Map<RelationSymbol, Iterable<Integer>> relevantIndices) {
		this.all = all;
		this.indices = indices;
		this.relevantIndices = relevantIndices;
	}

	@Override
	public Set<RelationSymbol> getSymbols() {
		return all.keySet();
	}

	@Override
	public Set<Term[]> getAll(RelationSymbol sym) {
		return all.get(sym);
	}

	@Override
	public Set<Term[]> get(Term[] key, int index) {
		return indices[index].lookup(key);
	}

	@Override
	public boolean add(RelationSymbol sym, Term[] args) {
		assert allNormal(args);
		if (!all.get(sym).add(args)) {
			return false;
		}
		for (Integer idx : relevantIndices.get(sym)) {
			indices[idx].add(args);
		}
		return true;
	}

	private boolean allNormal(Term[] args) {
		for (Term arg : args) {
			if (!arg.isGround() || arg.containsFunctionCall()) {
				return false;
			}
		}
		return true;
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
			Integer idx = m.get(key);
			if (idx == null) {
				idx = cnt++;
				m.put(key, idx);
			}
			return idx;
		}

		@Override
		public SortedIndexedFactDb build() {
			Map<RelationSymbol, Set<Term[]>> all = new LinkedHashMap<>();
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
			return new IndexedFactSet(pat, new ConcurrentSkipListSet<>(cmp));
		}

		public void clear() {
			s.clear();
		}

		private IndexedFactSet(BindingType[] pat, NavigableSet<Term[]> s) {
			this.pat = pat;
			this.s = s;
		}

		public void add(Term[] arr) {
			s.add(arr);
		}

		public Set<Term[]> lookup(Term[] arr) {
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
			return s.subSet(lower, true, upper, true);
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
