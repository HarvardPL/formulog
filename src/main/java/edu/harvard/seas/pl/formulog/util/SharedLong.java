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

public class SharedLong {

	private static class Box {
		long val;
	}

	private final Set<Box> boxes = Util.concurrentSet();

	private final ThreadLocal<Box> tl = ThreadLocal.withInitial(() -> {
		var box = new Box();
		boxes.add(box);
		return box;
	});

	public void increment() {
		tl.get().val++;
	}

	public void add(long delta) {
		if (delta == 0) {
			return;
		}
		tl.get().val += delta;
	}

	public long unsafeGet() {
		long sum = 0;
		for (var box : boxes) {
			sum += box.val;
		}
		return sum;
	}

}
