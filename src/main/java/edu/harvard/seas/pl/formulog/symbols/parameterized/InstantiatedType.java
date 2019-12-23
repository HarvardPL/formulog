//package edu.harvard.seas.pl.formulog.symbols.parameterized;
//
///*-
// * #%L
// * FormuLog
// * %%
// * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
// * %%
// * Licensed under the Apache License, Version 2.0 (the "License");
// * you may not use this file except in compliance with the License.
// * You may obtain a copy of the License at
// * 
// *      http://www.apache.org/licenses/LICENSE-2.0
// * 
// * Unless required by applicable law or agreed to in writing, software
// * distributed under the License is distributed on an "AS IS" BASIS,
// * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// * See the License for the specific language governing permissions and
// * limitations under the License.
// * #L%
// */
//
//import java.util.Map;
//
//import edu.harvard.seas.pl.formulog.types.Types;
//import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
//import edu.harvard.seas.pl.formulog.types.Types.Type;
//
//public class InstantiatedType implements PreType {
//
//	private final Type type;
//	
//	public InstantiatedType(Type type) {
//		this.type = type;
//		if (Types.containsTypeVarOrOpaqueType(type)) {
//			throw new IllegalArgumentException("Cannot instantiate a parameter with a type containing type variables or opaque types: " + type);
//		}
//	}
//
//	@Override
//	public PreType applySubst(Map<ParamVar, ParamElt> subst) {
//		return this;
//	}
//	
//	public Type getType() {
//		return type;
//	}
//
//	@Override
//	public boolean matchesParamSubKind(ParamSubKind kind) {
//		switch (kind) {
//		case ANY_TYPE:
//			return true;
//		case FUN:
//		case NAT:
//			return false;
//		case PRE_SMT_TYPE:
//			return Types.isPreSmtType(type);
//		case MODEL_FREE_TYPE:
//			return !Types.containsModelType(type);
//		case SMT_VAR:
//			return Types.isSmtVarType(type);
//		case SMT_VARS:
//			if (Types.isSmtVarType(type)) {
//				return true;
//			}
//			if (!Types.isTupleType(type)) {
//				return false;
//			}
//			AlgebraicDataType adt = (AlgebraicDataType) type;
//			for (Type typeArg : adt.getTypeArgs()) {
//				if (!Types.isSmtVarType(typeArg)) {
//					return false;
//				}
//			}
//			return true;
//		}
//		throw new AssertionError("impossible");
//	}
//	
//	@Override
//	public boolean containsParamVars() {
//		return false;
//	}
//	
//	@Override
//	public Type mkFinal() {
//		return type;
//	}
//
//	@Override
//	public int hashCode() {
//		final int prime = 31;
//		int result = 1;
//		result = prime * result + ((type == null) ? 0 : type.hashCode());
//		return result;
//	}
//
//	@Override
//	public boolean equals(Object obj) {
//		if (this == obj)
//			return true;
//		if (obj == null)
//			return false;
//		if (getClass() != obj.getClass())
//			return false;
//		InstantiatedType other = (InstantiatedType) obj;
//		if (type == null) {
//			if (other.type != null)
//				return false;
//		} else if (!type.equals(other.type))
//			return false;
//		return true;
//	}
//
//}
