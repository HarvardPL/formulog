package edu.harvard.seas.pl.formulog.types;

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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public final class Types {

	private Types() {
		throw new AssertionError();
	}

	public static interface Type {

		<I, O> O visit(TypeVisitor<I, O> visitor, I in);

		Type applySubst(Map<TypeVar, Type> subst);

		Type freshen();

		default boolean isVar() {
			return false;
		}

	}

	public static interface TypeVisitor<I, O> {

		O visit(TypeVar typeVar, I in);

		O visit(AlgebraicDataType algebraicType, I in);

		O visit(OpaqueType opaqueType, I in);

		O visit(TypeIndex typeIndex, I in);

	}

	public static class TypeVar implements Type, Comparable<TypeVar> {

		private static final Map<String, Integer> memo = new ConcurrentHashMap<>();
		private static final AtomicInteger cnt = new AtomicInteger();

		private final int id;

		private TypeVar(int id) {
			this.id = id;
		}

		public static TypeVar get(String id) {
			int i = Util.lookupOrCreate(memo, id, () -> cnt.getAndIncrement());
			return new TypeVar(i);
		}

		@Override
		public String toString() {
			return "'_" + id;
		}

		@Override
		public <I, O> O visit(TypeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + id;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			TypeVar other = (TypeVar) obj;
			if (id != other.id)
				return false;
			return true;
		}

		@Override
		public Type applySubst(Map<TypeVar, Type> subst) {
			return TypeChecker.lookupType(this, subst);
		}

		public static TypeVar fresh() {
			return new TypeVar(cnt.getAndIncrement());
		}

		@Override
		public boolean isVar() {
			return true;
		}

		@Override
		public int compareTo(TypeVar o) {
			return Integer.compare(this.id, o.id);
		}

		@Override
		public Type freshen() {
			return fresh();
		}

	}

	private static List<Type> freshen(List<Type> types) {
		return types.stream().map(Type::freshen).collect(Collectors.toList());
	}

	public static class AlgebraicDataType implements Type, Iterable<Type> {

		private final TypeSymbol sym;
		private final List<Type> typeArgs;
		private final AtomicReference<Set<ConstructorScheme>> constructors = new AtomicReference<>();

		private static final Map<Symbol, Pair<List<TypeVar>, Set<ConstructorScheme>>> memo = new ConcurrentHashMap<>();

		private AlgebraicDataType(TypeSymbol sym, List<Type> typeArgs) {
			this.sym = sym;
			this.typeArgs = new ArrayList<>(typeArgs);
			if (sym.getArity() != typeArgs.size()) {
				throw new IllegalArgumentException(
						"Arity of symbol " + sym + " does not match number of provided type parameters");
			}
			if (sym.isAlias()) {
				throw new IllegalArgumentException("Cannot create a type with alias symbol " + sym);
			}
		}

		public static AlgebraicDataType make(TypeSymbol sym, List<Type> typeArgs) {
			return new AlgebraicDataType(sym, typeArgs);
		}

		public static AlgebraicDataType make(TypeSymbol sym) {
			List<Type> typeVars = new ArrayList<>();
			for (int i = 0; i < sym.getArity(); ++i) {
				typeVars.add(TypeVar.fresh());
			}
			return make(sym, typeVars);
		}

		public static void setConstructors(TypeSymbol sym, List<TypeVar> typeParams,
				Collection<ConstructorScheme> constructors) {
			if (sym.isAlias()) {
				throw new IllegalArgumentException("Cannot set constructors for type alias symbol " + sym + ".");
			}
			if (typeParams.size() != (new HashSet<>(typeParams).size())) {
				throw new IllegalArgumentException("Each type variable must be unique.");
			}
			if (memo.put(sym, new Pair<>(typeParams, new HashSet<>(constructors))) != null) {
				throw new IllegalStateException("Cannot set the constructors for a type multiple times.");
			}
		}

		public boolean hasConstructors() {
			return memo.containsKey(sym);
		}

		public Set<ConstructorScheme> getConstructors() {
			Set<ConstructorScheme> s = constructors.get();
			if (s == null) {
				Pair<List<TypeVar>, Set<ConstructorScheme>> p = memo.get(sym);
				if (p == null) {
					throw new IllegalStateException("No constructors have been set for symbol " + sym + ".");
				}
				List<TypeVar> params = p.fst();
				Map<TypeVar, Type> subst = new HashMap<>();
				for (int i = 0; i < params.size(); ++i) {
					TypeVar x = params.get(i);
					Type t = typeArgs.get(i);
					// XXX This is to avoid cycles in subst, but is obviously fragile
					if (!x.equals(t)) {
						subst.put(x, t);
					}
				}
				s = new HashSet<>();
				for (ConstructorScheme c : p.snd()) {
					List<Type> newArgs = new ArrayList<>();
					for (Type t : c.getTypeArgs()) {
						newArgs.add(t.applySubst(subst));
					}
					s.add(new ConstructorScheme(c.getSymbol(), newArgs, c.getGetterSymbols()));
				}
				if (!constructors.compareAndSet(null, s)) {
					s = constructors.get();
				}
			}
			return s;
		}

		public TypeSymbol getSymbol() {
			return sym;
		}

		@Override
		public Iterator<Type> iterator() {
			return typeArgs.iterator();
		}

		@Override
		public String toString() {
			if (typeArgs.isEmpty()) {
				return sym.toString();
			}
			if (typeArgs.size() == 1) {
				return typeArgs.get(0) + " " + sym;
			}
			StringBuilder sb = new StringBuilder("(");
			Iterator<Type> it = typeArgs.iterator();
			sb.append(it.next());
			while (it.hasNext()) {
				sb.append(", " + it.next());
			}
			sb.append(") " + sym);
			return sb.toString();
		}

		@Override
		public <I, O> O visit(TypeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((sym == null) ? 0 : sym.hashCode());
			result = prime * result + ((typeArgs == null) ? 0 : typeArgs.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			AlgebraicDataType other = (AlgebraicDataType) obj;
			if (sym == null) {
				if (other.sym != null)
					return false;
			} else if (!sym.equals(other.sym))
				return false;
			if (typeArgs == null) {
				if (other.typeArgs != null)
					return false;
			} else if (!typeArgs.equals(other.typeArgs))
				return false;
			return true;
		}

		public List<Type> getTypeArgs() {
			return typeArgs;
		}

		@Override
		public Type applySubst(Map<TypeVar, Type> subst) {
			List<Type> newTypes = new ArrayList<>();
			for (Type t : typeArgs) {
				newTypes.add(t.applySubst(subst));
			}
			return make(sym, newTypes);
		}

		@Override
		public Type freshen() {
			return make(sym, Types.freshen(typeArgs));
		}

		public static class ConstructorScheme {

			private final ConstructorSymbol sym;
			private final List<Type> typeArgs;
			private final List<ConstructorSymbol> getterSyms;

			public ConstructorScheme(ConstructorSymbol sym, List<Type> typeArgs, List<ConstructorSymbol> getterSyms) {
				this.sym = sym;
				this.typeArgs = typeArgs;
				this.getterSyms = getterSyms;
				assert sym != null;
			}

			public ConstructorSymbol getSymbol() {
				return sym;
			}

			public List<Type> getTypeArgs() {
				return typeArgs;
			}

			public List<ConstructorSymbol> getGetterSymbols() {
				return getterSyms;
			}

			@Override
			public int hashCode() {
				final int prime = 31;
				int result = 1;
				result = prime * result + ((getterSyms == null) ? 0 : getterSyms.hashCode());
				result = prime * result + ((sym == null) ? 0 : sym.hashCode());
				result = prime * result + ((typeArgs == null) ? 0 : typeArgs.hashCode());
				return result;
			}

			@Override
			public boolean equals(Object obj) {
				if (this == obj)
					return true;
				if (obj == null)
					return false;
				if (getClass() != obj.getClass())
					return false;
				ConstructorScheme other = (ConstructorScheme) obj;
				if (getterSyms == null) {
					if (other.getterSyms != null)
						return false;
				} else if (!getterSyms.equals(other.getterSyms))
					return false;
				if (sym == null) {
					if (other.sym != null)
						return false;
				} else if (!sym.equals(other.sym))
					return false;
				if (typeArgs == null) {
					if (other.typeArgs != null)
						return false;
				} else if (!typeArgs.equals(other.typeArgs))
					return false;
				return true;
			}

		}

	}

	public static class OpaqueType implements Type {
		/*
		 * This class is used (exclusively) during type checking.
		 */

		private static final AtomicInteger cnt = new AtomicInteger();
		private final int id;

		private OpaqueType() {
			id = cnt.getAndIncrement();
		}

		public static OpaqueType get() {
			return new OpaqueType();
		}

		@Override
		public <I, O> O visit(TypeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public Type applySubst(Map<TypeVar, Type> subst) {
			return this;
		}

		@Override
		public String toString() {
			return "Opaque" + id;
		}

		@Override
		public Type freshen() {
			return get();
		}

	}

	public static class TypeIndex implements Type {

		private final int index;

		public TypeIndex(int index) {
			this.index = index;
		}

		public static TypeIndex make(int index) {
			return new TypeIndex(index);
		}

		@Override
		public <I, O> O visit(TypeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public Type applySubst(Map<TypeVar, Type> subst) {
			return this;
		}

		@Override
		public Type freshen() {
			return this;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + index;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			TypeIndex other = (TypeIndex) obj;
			if (index != other.index)
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "[" + index + "]";
		}

		public int getIndex() {
			return index;
		}

	}

	// Helpers /////////////////////////////////////////////////////////////////

	public static Set<TypeVar> getTypeVars(Type t) {
		return getTypeVars(Collections.singletonList(t));
	}

	public static Set<TypeVar> getTypeVars(Collection<Type> t) {
		Set<TypeVar> set = new HashSet<>();
		getTypeVars(t, set);
		return set;
	}

	private static void getTypeVars(Type t, Set<TypeVar> acc) {
		t.visit(new TypeVisitor<Void, Void>() {

			@Override
			public Void visit(TypeVar typeVar, Void in) {
				acc.add(typeVar);
				return null;
			}

			@Override
			public Void visit(OpaqueType opaqueType, Void in) {
				return null;
			}

			@Override
			public Void visit(AlgebraicDataType namedType, Void in) {
				getTypeVars(namedType.getTypeArgs(), acc);
				return null;
			}

			@Override
			public Void visit(TypeIndex typeIndex, Void in) {
				return null;
			}

		}, null);
	}

	private static void getTypeVars(Collection<Type> types, Set<TypeVar> acc) {
		for (Type t : types) {
			getTypeVars(t, acc);
		}
	}
	
	public static boolean containsTypeVarOrOpaqueType(Type t) {
		return t.visit(new TypeVisitor<Void, Boolean>() {

			@Override
			public Boolean visit(TypeVar typeVar, Void in) {
				return true;
			}

			@Override
			public Boolean visit(AlgebraicDataType algebraicType, Void in) {
				for (Type ty : algebraicType.getTypeArgs()) {
					if (ty.visit(this, in)) {
						return true;
					}
				}
				return false;
			}

			@Override
			public Boolean visit(OpaqueType opaqueType, Void in) {
				return true;
			}

			@Override
			public Boolean visit(TypeIndex typeIndex, Void in) {
				return false;
			}
			
		}, null);
	}

}
