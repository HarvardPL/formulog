//package edu.harvard.seas.pl.formulog.symbols.parameterized;
//
//import edu.harvard.seas.pl.formulog.types.Types.Type;
//
//public class TypeParam implements ParamElt {
//
//	private final Type type;
//	private final ParamKind kind;
//	
//	public TypeParam(Type type) {
//		this.type = type;
//	}
//
//	@Override
//	public Type getType() {
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
//		TypeParam other = (TypeParam) obj;
//		if (type == null) {
//			if (other.type != null)
//				return false;
//		} else if (!type.equals(other.type))
//			return false;
//		return true;
//	}
//
//	@Override
//	public String toString() {
//		return "TypeParam [type=" + type + "]";
//	}
//
//}
