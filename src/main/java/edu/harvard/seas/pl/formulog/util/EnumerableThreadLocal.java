package edu.harvard.seas.pl.formulog.util;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2023 President and Fellows of Harvard College
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

import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Supplier;

public class EnumerableThreadLocal<T> {

	private final Set<T> items = Util.concurrentSet();
	private final ThreadLocal<T> tl;

	public EnumerableThreadLocal(Supplier<T> f) {
		tl = ThreadLocal.withInitial(() -> {
			var item = f.get();
			items.add(item);
			return item;
		});
	}
	
	public T get() {
		return tl.get();
	}

	public void forEach(Consumer<T> f) {
		items.forEach(f);
	}

}
