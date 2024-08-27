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
package edu.harvard.seas.pl.formulog.util;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;
import java.util.Map;

public class StackMap<K, V> {

  private final Deque<Map<K, V>> stack = new ArrayDeque<>();

  public synchronized void push(Map<K, V> m) {
    stack.addFirst(m);
  }

  public synchronized Map<K, V> pop() {
    return stack.remove();
  }

  public synchronized V get(K k) {
    for (Iterator<Map<K, V>> it = stack.iterator(); it.hasNext(); ) {
      Map<K, V> m = it.next();
      V v = m.get(k);
      if (v != null) {
        return v;
      }
    }
    return null;
  }

  public synchronized V put(K k, V v) {
    return stack.getFirst().put(k, v);
  }
}
