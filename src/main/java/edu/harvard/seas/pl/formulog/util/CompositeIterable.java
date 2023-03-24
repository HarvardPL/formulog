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

import java.util.ArrayDeque;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Queue;

public class CompositeIterable<T> implements Iterable<T> {

	private final Iterable<Iterable<T>> its;

	public CompositeIterable(Iterable<Iterable<T>> its) {
		this.its = its;
	}

	@Override
	public Iterator<T> iterator() {
		return new CompositeIterator();
	}

	private final class CompositeIterator implements Iterator<T> {

		private final Queue<Iterator<T>> iterators;

		public CompositeIterator() {
			Queue<Iterator<T>> l = new ArrayDeque<>();
			for (Iterable<T> it : its) {
				l.add(it.iterator());
			}
			this.iterators = l;

		}

		private boolean load() {
			if (iterators.isEmpty()) {
				return false;
			}
			if (iterators.peek().hasNext()) {
				return true;
			}
			iterators.remove();
			return load();
		}

		@Override
		public synchronized boolean hasNext() {
			return load();
		}

		@Override
		public synchronized T next() {
			if (!load()) {
				throw new NoSuchElementException();
			}
			return iterators.peek().next();
		}

	}

}
