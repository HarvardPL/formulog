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

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;

public class TypeAlias {

	private final Symbol sym;
	private final List<TypeVar> params;
	private final Type type;

	public TypeAlias(Symbol sym, List<TypeVar> params, Type type) {
		this.sym = sym;
		this.params = params;
		this.type = type;
		if (!sym.getSymbolType().equals(SymbolType.TYPE_ALIAS)) {
			throw new IllegalArgumentException("Cannot create an alias for non-type alias symbol " + sym);
		}
		if (this.sym.getArity() != this.params.size()) {
			throw new IllegalArgumentException(
					"Mismatch between symbol arity and number of type parameters: " + this.sym);
		}
		if (!Types.getTypeVars(this.type).containsAll(this.params)) {
			throw new IllegalArgumentException("Unbound type variable in definition of type: " + this.sym);
		}
	}

	public static TypeAlias get(Symbol sym, List<TypeVar> params, Type type) {
		return new TypeAlias(sym, params, type);
	}

	public Symbol getSymbol() {
		return sym;
	}

	public int getNumberOfParams() {
		return params.size();
	}

	public Type getParam(int idx) {
		if (idx < 0 || idx >= params.size()) {
			throw new IllegalArgumentException("Out of bounds parameter: " + idx);
		}
		return params.get(idx);
	}

	@Override
	public String toString() {
		if (params.isEmpty()) {
			return sym.toString() + " = " + type;
		}
		if (params.size() == 1) {
			return params.get(0) + " " + sym + " = " + type;
		}
		StringBuilder sb = new StringBuilder('(');
		Iterator<TypeVar> it = params.iterator();
		sb.append(it.next());
		while (it.hasNext()) {
			sb.append(", " + it.next());
		}
		sb.append(") " + sym + " = " + type);
		return sb.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		result = prime * result + ((sym == null) ? 0 : sym.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
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
		TypeAlias other = (TypeAlias) obj;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		if (sym == null) {
			if (other.sym != null)
				return false;
		} else if (!sym.equals(other.sym))
			return false;
		if (type == null) {
			if (other.type != null)
				return false;
		} else if (!type.equals(other.type))
			return false;
		return true;
	}

	public List<TypeVar> getParams() {
		return params;
	}

	public Type instantiate(List<Type> paramTypes) {
		if (paramTypes.size() != params.size()) {
			throw new IllegalArgumentException();
		}
		Map<TypeVar, Type> subst = new HashMap<>();
		for (int i = 0; i < params.size(); ++i) {
			TypeChecker.addBinding(params.get(i), paramTypes.get(i), subst);
		}
		return type.applySubst(subst);
	}

	public Type getType() {
		return type;
	}

}
