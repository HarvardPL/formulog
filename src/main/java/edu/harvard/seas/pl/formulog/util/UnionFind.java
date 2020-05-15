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


import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class UnionFind<T> {

	private final Map<T, T> m = new HashMap<>();
	
	public boolean contains(T t) {
		return m.containsKey(t);
	}
	
	public boolean add(T t) {
		return m.putIfAbsent(t, t) == null;
	}
	
	public void union(T t1, T t2) {
		t1 = find(t1);
		t2 = find(t2);
		m.put(t1, t2);
	}
	
	public T find(T t) {
		assert contains(t);
		T prev = null;
		while (!t.equals(prev)) {
			prev = t;
			t = m.get(prev);
		}
		return t;
	}
	
	public Set<T> members() {
		return m.keySet();
	}
	
}
