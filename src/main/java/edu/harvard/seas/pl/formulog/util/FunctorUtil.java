package edu.harvard.seas.pl.formulog.util;

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

import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

import edu.harvard.seas.pl.formulog.ast.Functor;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.symbols.Symbol;

public final class FunctorUtil {

	private FunctorUtil() {
		throw new AssertionError();
	}

	public static String toString(Symbol sym, Term[] args) {
		StringBuilder sb = new StringBuilder(sym.toString());
		int arity = sym.getArity();
		if (arity > 0) {
			sb.append('(');
			for (int i = 0; i < arity; ++i) {
				sb.append(args[i]);
				if (i < arity - 1) {
					sb.append(", ");
				}
			}
			sb.append(')');
		}
		return sb.toString();
	}

	public static class Memoizer<F extends Functor> {

		private final Map<Object, Object> memo = new ConcurrentHashMap<>();

		@SuppressWarnings("unchecked")
		public F lookupOrCreate(Symbol sym, Term[] args, Supplier<F> constructor) {
			if (sym.getArity() != args.length) {
				throw new IllegalArgumentException("Symbol " + sym + " has arity " + sym.getArity() + " but args "
						+ Arrays.toString(args) + " have length " + args.length);
			}
			Map<Object, Object> m = memo;
			Object k = sym;
			for (int i = 0; i < args.length; ++i) {
				m = (Map<Object, Object>) Util.lookupOrCreate(m, k, () -> new ConcurrentHashMap<>());
				k = args[i];
			}
			return (F) Util.lookupOrCreate(m, k, () -> constructor.get());
		}

	}

}
