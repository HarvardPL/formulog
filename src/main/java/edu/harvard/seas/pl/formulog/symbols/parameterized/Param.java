package edu.harvard.seas.pl.formulog.symbols.parameterized;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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
			return true;
		case MODEL_FREE_TYPE:
			return !Types.containsModelType(type);
		case NAT:
			return type instanceof TypeIndex;
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
	
	public static List<Param> instantiate(Iterable<ParamKind> kinds) {
		List<Param> params = new ArrayList<>();
		for (ParamKind kind : kinds) {
			params.add(new Param(TypeVar.fresh(), kind));
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

	public List<Param> expandAsFpAlias() {
		if (!kind.equals(ParamKind.NAT) || !isGround()) {
			return Collections.singletonList(this);
		}
		TypeIndex nat = (TypeIndex) type;
		switch (nat.getIndex()) {
		case 16:
			return Arrays.asList(Param.nat(5), Param.nat(11));
		case 32:
			return Arrays.asList(Param.nat(8), Param.nat(24));
		case 64:
			return Arrays.asList(Param.nat(11), Param.nat(53));
		case 128:
			return Arrays.asList(Param.nat(15), Param.nat(113));
		default:
			throw new IllegalArgumentException("Illegal floating point width alias: " + nat);
		}
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
