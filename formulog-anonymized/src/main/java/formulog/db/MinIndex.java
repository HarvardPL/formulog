package formulog.db;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class MinIndex {

	private MinIndex() {
		throw new AssertionError("impossible");
	}
	
	public static <T> Map<Set<T>, Iterable<T>> compute(Set<T> domain, Set<Set<T>> searches) {
		MinChainCover<Set<T>> mcc = new MinChainCover<>((x, y) -> y.containsAll(x));
		Iterable<Iterable<Set<T>>> chains = mcc.compute(searches); 
		Map<Set<T>, Iterable<T>> idxs = new HashMap<>();
		for (Iterable<Set<T>> chain : chains) {
			List<T> idx = computeIndex(chain);
			padIndex(idx, domain);
			for (Set<T> search : chain) {
				Iterable<T> other = idxs.put(search, idx);
				assert other == null;
			}
		}
		return idxs;
	}
	
	private static <T> void padIndex(List<T> idx, Set<T> domain) {
		Set<T> seen = new HashSet<>(idx);
		for (T elt : domain) {
			if (seen.add(elt)) {
				idx.add(elt);
			}
		}
	}

	private static <T> List<T> computeIndex(Iterable<Set<T>> chain) {
		List<T> index = new ArrayList<>();
		Set<T> prev = Collections.emptySet();
		for (Set<T> s : chain) {
			for (T elt : s) {
				if (!prev.contains(elt)) {
					index.add(elt);
				}
			}
			prev = s;
		}
		return index;
	}
	
	public static void main(String[] args) {
		Set<String> s1 = new HashSet<>(Arrays.asList("x"));
		Set<String> s2 = new HashSet<>(Arrays.asList("x", "y"));
		Set<String> s3 = new HashSet<>(Arrays.asList("x", "z"));
		Set<String> s4 = new HashSet<>(Arrays.asList("x", "y", "z"));
		Set<Set<String>> searches = new HashSet<>(Arrays.asList(s1, s2, s3, s4));
		System.out.println(MinIndex.compute(s4, searches));
	}

}
