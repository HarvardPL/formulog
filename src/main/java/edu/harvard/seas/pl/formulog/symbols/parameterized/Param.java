package edu.harvard.seas.pl.formulog.symbols.parameterized;

/*-
 * #%L
 * FormuLog
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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;

public class Param {

	private final Type type;
	private final ParamKind kind;

	public Param(Type type, ParamKind kind) {
		this.type = type;
		this.kind = kind;
		if (!check()) {
			throw new IllegalArgumentException("Cannot instantiate parameter of kind " + kind + " with type " + type);
		}
	}
	
	private boolean check() {
		if (type.isVar()) {
			return true;
		}
		switch (kind) {
		case ANY_TYPE:
			return !type.isIndex();
		case WILD_CARD:
			return true;
		case SMT_REPRESENTABLE_TYPE:
			return Types.isSmtRepresentable(type);
		case NAT:
			return type.isIndex();
		case PRE_SMT_TYPE:
			return Types.mayBePreSmtType(type);
		case SMT_VAR:
			return Types.isSmtVarType(type);
		case SMT_VARS:
			if (Types.isSmtVarType(type)) {
				return true;
			}
			if (!Types.isTupleType(type)) {
				return false;
			}
			for (Type typeArg : ((AlgebraicDataType) type).getTypeArgs()) {
				if (!typeArg.isVar() && !Types.isSmtVarType(type)) {
					return false;
				}
			}
			return true;
		}
		throw new AssertionError("impossible");
	}
	
	public Type getType() {
		return type;
	}
	
	public ParamKind getKind() {
		return kind;
	}
	
	boolean isGround() {
		return !Types.containsTypeVarOrOpaqueType(getType());
	}
	
	public static List<Param> wildCards(int howMany) {
		List<Param> params = new ArrayList<>();
		for (int i = 0; i < howMany; ++i) {
			params.add(wildCard());
		}
		return params;
	}
	
	public static List<Param> applySubst(Iterable<Param> params, Map<TypeVar, Type> subst) {
		List<Param> newParams = new ArrayList<>();
		for (Param param : params) {
			newParams.add(new Param(param.getType().applySubst(subst), param.getKind()));
		}
		return newParams;
	}

	public static Param nat(int index) {
		return new Param(TypeIndex.make(index), ParamKind.NAT);
	}
	
	public static Param nat(Type type) {
		return new Param(type, ParamKind.NAT);
	}
	
	public static Param wildCard() {
		return new Param(TypeVar.fresh(), ParamKind.WILD_CARD);
	}
	
	public static Param wildCard(Type type) {
		return new Param(type, ParamKind.WILD_CARD);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((kind == null) ? 0 : kind.hashCode());
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
		Param other = (Param) obj;
		if (kind != other.kind)
			return false;
		if (type == null) {
			if (other.type != null)
				return false;
		} else if (!type.equals(other.type))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return type + ":" + kind;
	}
	
}
