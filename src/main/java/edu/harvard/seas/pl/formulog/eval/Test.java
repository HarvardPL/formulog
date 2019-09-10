package edu.harvard.seas.pl.formulog.eval;

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

import java.util.Spliterator;
import java.util.TreeSet;

public class Test {

	public static void main(String[] args) {
		TreeSet<Integer> s = new TreeSet<>();
		for (int i = 0; i < 256; ++i) {
			s.add(i);
		}
		Spliterator<Integer> split = s.spliterator();
		while (true) {
			System.out.println("Estimated size " + split.estimateSize());
			Spliterator<Integer> split2 = split.trySplit();
			if (split2 == null) {
				break;
			}
		}
		split.forEachRemaining(i -> System.out.println(i));
	}

}
