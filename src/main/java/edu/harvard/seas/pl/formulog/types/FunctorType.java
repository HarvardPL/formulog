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
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.util.Util;

public class FunctorType implements Type {

	private final List<Type> argTypes;
	private final Type retType;

	public FunctorType(List<Type> argTypes, Type retType) {
		this.argTypes = argTypes;
		this.retType = retType;
	}
	
	public FunctorType(Type...types) {
		assert types.length > 0;
		argTypes = new ArrayList<>(Arrays.asList(types));
		retType = this.argTypes.remove(types.length - 1);
	}

	public List<Type> getArgTypes() {
		return argTypes;
	}

	public Type getRetType() {
		return retType;
	}

	public FunctorType freshen() {
		Map<TypeVar, TypeVar> subst = new HashMap<>();
		TypeVisitor<Void, Type> visitor = new TypeVisitor<Void, Type>() {

			@Override
			public Type visit(TypeVar typeVar, Void in) {
				return Util.lookupOrCreate(subst, typeVar, () -> TypeVar.fresh());
			}

			@Override
			public Type visit(OpaqueType opaqueType, Void in) {
				throw new AssertionError();
			}

			private List<Type> processTypeList(List<Type> types) {
				List<Type> newTypes = new ArrayList<>();
				for (Type t : types) {
					newTypes.add(t.visit(this, null));
				}
				return newTypes;
			}

			@Override
			public Type visit(AlgebraicDataType namedType, Void in) {
				return AlgebraicDataType.make(namedType.getSymbol(), processTypeList(namedType.getTypeArgs()));
			}

			@Override
			public Type visit(TypeIndex typeIndex, Void in) {
				return typeIndex;
			}

		};
		List<Type> newArgTypes = new ArrayList<>();
		for (Type t : argTypes) {
			newArgTypes.add(t.visit(visitor, null));
		}
		Type newRetType = retType.visit(visitor, null);
		return new FunctorType(newArgTypes, newRetType);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((argTypes == null) ? 0 : argTypes.hashCode());
		result = prime * result + ((retType == null) ? 0 : retType.hashCode());
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
		FunctorType other = (FunctorType) obj;
		if (argTypes == null) {
			if (other.argTypes != null)
				return false;
		} else if (!argTypes.equals(other.argTypes))
			return false;
		if (retType == null) {
			if (other.retType != null)
				return false;
		} else if (!retType.equals(other.retType))
			return false;
		return true;
	}

	@Override
	public <I, O> O visit(TypeVisitor<I, O> visitor, I in) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Type applySubst(Map<TypeVar, Type> subst) {
		List<Type> newArgTypes = argTypes.stream().map(t -> t.applySubst(subst)).collect(Collectors.toList());
		Type newRetType = retType.applySubst(subst);
		return new FunctorType(newArgTypes, newRetType);
	}
	
	@Override
	public String toString() {
		String s = "(";
		for (Iterator<Type> it = argTypes.iterator(); it.hasNext();) {
			s += it.next();
			if (it.hasNext()) {
				s += ", ";
			}
		}
		s += ") -> " + retType;
		return s;
	}

}
