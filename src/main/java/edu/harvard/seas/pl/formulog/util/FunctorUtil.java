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

import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

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

	// public static class Memoizer<F extends Functor> {
	//
	// private final Map<Object, Object> memo = new ConcurrentHashMap<>();
	//
	// @SuppressWarnings("unchecked")
	// public F lookupOrCreate(Symbol sym, Term[] args, Supplier<F> constructor) {
	// if (sym.getArity() != args.length) {
	// throw new IllegalArgumentException("Symbol " + sym + " has arity " +
	// sym.getArity() + " but args "
	// + Arrays.toString(args) + " have length " + args.length);
	// }
	// Map<Object, Object> m = memo;
	// Object k = sym;
	// for (int i = 0; i < args.length; ++i) {
	// m = (Map<Object, Object>) Util.lookupOrCreate(m, k, () -> new
	// ConcurrentHashMap<>());
	// k = args[i];
	// }
	// return (F) Util.lookupOrCreate(m, k, () -> constructor.get());
	// }
	//
	// }

	public static class Memoizer<T extends Term> {

		private final Map<Key, T> memo = new ConcurrentHashMap<>();

		public T lookupOrCreate(Symbol sym, Term[] args, Supplier<T> constructor) {
			if (sym.getArity() != args.length) {
				throw new IllegalArgumentException("Symbol " + sym + " has arity " + sym.getArity() + " but args "
						+ Arrays.toString(args) + " have arity " + args.length);
			}
			Key key = new Key(sym, args);
			T f = memo.get(key);
			if (f == null) {
				f = constructor.get();
				T f2 = memo.putIfAbsent(key, f);
				if (f2 != null) {
					f = f2;
				}
			}
			return f;
		}

		private static class Key {

			private final Symbol sym;
			private final Term[] args;
			private final int hashCode;

			public Key(Symbol sym, Term[] args) {
				this.sym = sym;
				this.args = args;
				final int prime = 31;
				int result = 1;
				result = prime * result + Arrays.hashCode(args);
				result = prime * result + ((sym == null) ? 0 : sym.hashCode());
				hashCode = result;
			}

			@Override
			public int hashCode() {
				return hashCode;
			}

			@Override
			public boolean equals(Object obj) {
				if (this == obj)
					return true;
				if (obj == null)
					return false;
				if (getClass() != obj.getClass())
					return false;
				Key other = (Key) obj;
				if (hashCode != other.hashCode) {
					return false;
				}
				if (sym == null) {
					if (other.sym != null)
						return false;
				} else if (!sym.equals(other.sym))
					return false;
				if (!Arrays.equals(args, other.args))
					return false;
				return true;
			}

		}

	}

}
