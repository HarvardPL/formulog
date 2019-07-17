package edu.harvard.seas.pl.formulog.db;

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
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.concurrent.ConcurrentSkipListSet;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.ArrayWrapper;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.Predicate;

public class SortedIndexedFactDb implements IndexedFactDB {

	@Override
	public Set<RelationSymbol> getSymbols() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Term[]> getAll(RelationSymbol sym) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Term[]> get(Term[] key, int index) {
		// TODO Auto-generated method stub
		return null;
	}

	public static class SortedIndexedFactDbBuilder implements IndexedFactDbBuilder<SortedIndexedFactDb> {

		private int cnt = 0;
		private final Map<RelationSymbol, Map<ArrayWrapper<Boolean>, Integer>> pats = new HashMap<>();

		@Override
		public synchronized int makeIndex(Predicate atom) {
			boolean[] pat = atom.getBindingPattern();
			Boolean[] pat2 = new Boolean[pat.length];
			for (int i = 0; i < pat.length; ++i) {
				pat2[i] = pat[i];
			}
			Map<ArrayWrapper<Boolean>, Integer> m = Util.lookupOrCreate(pats, atom.getSymbol(), () -> new HashMap<>());
			ArrayWrapper<Boolean> key = new ArrayWrapper<>(pat2);
			Integer idx = m.get(key);
			if (idx == null) {
				idx = cnt++;
				m.put(key, idx);
			}
			return idx;
		}

		@Override
		public SortedIndexedFactDb build() {
			// TODO Auto-generated method stub
			return null;
		}

	}

	private static class IndexedFactSet {

		private final boolean[] pat;
		private final Comparator<Term[]> cmp;
		private final NavigableSet<Term[]> s;
	
		public IndexedFactSet make(boolean[] pat) {
			int[] order = new int[pat.length];
			int pos = 0;
			for (int i = 0; i < pat.length; ++i) {
				if (pat[i]) {
					order[pos] = i;
					pos++;
				}
			}
			for (int i = 0; i < pat.length; ++i) {
				if (!pat[i]) {
					order[pos] = i;
					pos++;
				}
			}
			Comparator<Term[]> cmp = new ArrayComparator<>(order, null);
			return new IndexedFactSet(pat, cmp);
		}
		
		private IndexedFactSet(boolean[] pat, Comparator<Term[]> cmp) {
			this.pat = pat;
			this.cmp = cmp;
			s = new ConcurrentSkipListSet<>(cmp);
		}
		
		public void add(Term[] arr) {
			s.add(arr);
		}
		
		public Set<Term[]> lookup(Term[] arr) {
			Term[] lower = new Term[arr.length];
			Term[] upper = new Term[arr.length];
			for (int i = 0; i < arr.length; ++i) {
				if (pat[i]) {
					lower[i] = arr[i];
					upper[i] = arr[i];
				} else {
					lower[i] = Terms.minTerm;
					upper[i] = Terms.maxTerm;
				}
			}
			return s.subSet(lower, true, upper, true);
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

}
