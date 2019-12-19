package edu.harvard.seas.pl.formulog.symbols;

import edu.harvard.seas.pl.formulog.types.BuiltInTypesFactory;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;

public class NatPreIndex implements TypePreIndex {

	public static final NatPreIndex a = new NatPreIndex(BuiltInTypesFactory.a);
	public static final NatPreIndex b = new NatPreIndex(BuiltInTypesFactory.b);
	public static final NatPreIndex c = new NatPreIndex(BuiltInTypesFactory.c);
	public static final NatPreIndex d = new NatPreIndex(BuiltInTypesFactory.d);
	
	private final TypeVar var;
	
	public NatPreIndex(TypeVar var) {
		this.var = var;
	}

	@Override
	public void check(Type type) throws TypeException {
		throw new UnsupportedOperationException();
	}

	@Override
	public TypeVar getTypeVar() {
		return var;
	}

	@Override
	public TypePreIndex freshen() {
		return new NatPreIndex(var.freshen());
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((var == null) ? 0 : var.hashCode());
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
		NatPreIndex other = (NatPreIndex) obj;
		if (var == null) {
			if (other.var != null)
				return false;
		} else if (!var.equals(other.var))
			return false;
		return true;
	}

}
