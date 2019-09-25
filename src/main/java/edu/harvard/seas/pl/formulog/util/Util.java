package edu.harvard.seas.pl.formulog.util;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.UserPredicate;

public final class Util {

	private Util() {
		throw new AssertionError();
	}

	public static <K, V> V lookupOrCreate(Map<K, V> m, K k, Supplier<V> cnstr) {
		V v = m.get(k);
		if (v == null) {
			v = cnstr.get();
			V u = m.putIfAbsent(k, v);
			if (u != null) {
				v = u;
			}
		}
		return v;
	}

	public static <T> Iterable<T> i2i(Iterator<T> it) {
		return () -> it;
	}

	public static <K> Set<K> concurrentSet() {
		return Collections.newSetFromMap(new ConcurrentHashMap<>());
	}

	public static <T> List<T> iterableToList(Iterable<T> it) {
		List<T> l = new ArrayList<>();
		it.forEach(l::add);
		return l;
	}

	public static <A, B> List<B> map(List<A> xs, Function<A, B> f) {
		return xs.stream().map(f).collect(Collectors.toList());
	}

	public static void printSortedFacts(Iterable<UserPredicate> facts, PrintStream out) {
		Util.iterableToList(facts).stream().map(a -> {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			PrintStream ps = new PrintStream(baos);
			ps.print(a);
			return baos.toString();
		}).sorted().forEach(s -> out.println(s));
	}

	public static <K, V> Map<K, V> fillMapWithFutures(Map<K, Future<V>> futures, Map<K, V> m)
			throws InterruptedException, ExecutionException {
		for (Map.Entry<K, Future<V>> e : futures.entrySet()) {
			m.put(e.getKey(), e.getValue().get());
		}
		return m;
	}

	public static class IterableOfIterables<T> implements Iterable<Iterable<T>> {

		private final Iterable<T> iterable;
		private final int size;

		public IterableOfIterables(Iterable<T> iterable, int size) {
			this.iterable = iterable;
			this.size = size;
		}

		@Override
		public Iterator<Iterable<T>> iterator() {
			Iterator<T> it = iterable.iterator();
			return new Iterator<Iterable<T>>() {

				@Override
				public boolean hasNext() {
					return it.hasNext();
				}

				@Override
				public Iterable<T> next() {
					assert hasNext();
					List<T> l = new ArrayList<>(size);
					for (int i = 0; i < size && it.hasNext(); ++i) {
						l.add(it.next());
					}
					return l;
				}

			};
		}

		@Override
		public String toString() {
			String s = "{";
			for (Iterator<Iterable<T>> it = iterator(); it.hasNext();) {
				s += it.next();
				if (it.hasNext()) {
					s += ",";
				}
			}
			return s + "}";
		}

		public String toString(Function<T, String> printer) {
			String s = "{";
			for (Iterator<Iterable<T>> it = iterator(); it.hasNext();) {
				s += " {";
				for (Iterator<T> it2 = it.next().iterator(); it2.hasNext();) {
					s += printer.apply(it2.next());
					if (it2.hasNext()) {
						s += ", ";
					}
				}
				s += "} ";
				if (it.hasNext()) {
					s += ", ";
				}
			}
			return s + "}";

		}

	}

	public static <T> Iterable<Iterable<T>> splitIterable(Iterable<T> iterable, int segmentSize) {
		return new IterableOfIterables<>(iterable, segmentSize);
	}

}
