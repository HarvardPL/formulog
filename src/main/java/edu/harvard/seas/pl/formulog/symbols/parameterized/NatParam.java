//package edu.harvard.seas.pl.formulog.symbols.parameterized;
//
//import java.util.Arrays;
//import java.util.List;
//
//import edu.harvard.seas.pl.formulog.types.Types.Type;
//import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
//import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
//
//public class NatParam implements ParamElt {
//
//	private final Type nat;
//
//	public NatParam(int nat) {
//		this(new TypeIndex(nat));
//		if (nat < 0) {
//			throw new IllegalArgumentException("Parameter cannot be less than zero.");
//		}
//	}
//	
//	public NatParam(TypeIndex nat) {
//		this.nat = nat;
//	}
//	
//	public NatParam(TypeVar x) {
//		this.nat = x;
//	}
//
//	@Override
//	public Type getType() {
//		return nat;
//	}
//	
//	public List<NatParam> expandAsFpAlias() {
//		assert isGround();
//		switch (((TypeIndex) nat).getIndex()) {
//		case 16:
//			return Arrays.asList(new NatParam(5), new NatParam(11));
//		case 32:
//			return Arrays.asList(new NatParam(8), new NatParam(24));
//		case 64:
//			return Arrays.asList(new NatParam(11), new NatParam(53));
//		case 128:
//			return Arrays.asList(new NatParam(15), new NatParam(113));
//		default:
//			throw new IllegalArgumentException("Illegal floating point width alias: " + nat);
//		}
//	}
//
//	@Override
//	public int hashCode() {
//		final int prime = 31;
//		int result = 1;
//		result = prime * result + ((nat == null) ? 0 : nat.hashCode());
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
//		NatParam other = (NatParam) obj;
//		if (nat == null) {
//			if (other.nat != null)
//				return false;
//		} else if (!nat.equals(other.nat))
//			return false;
//		return true;
//	}
//
//	@Override
//	public String toString() {
//		return "NatParam [nat=" + nat + "]";
//	}
//
//}
