package edu.harvard.seas.pl.formulog.ast;

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface Primitive<T> extends Term {

	T getVal();
	
	@Override
	default <I, O> O visit(TermVisitor<I, O> v, I in) {
		return v.visit(this, in);
	}

	@Override
	default <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E {
		return v.visit(this, in);
	}

	@Override
	public default boolean containsFunctionCall() {
		return false;
	}

	@Override
	public default Term applySubstitution(Substitution s) {
		return this;
	}
	
	@Override
	public default Term reduce(Substitution s) {
		return this;
	}
	
	@Override
	public default Term normalize(Substitution s) {
		return this;
	}
	
	@Override
	public default boolean isGround() {
		return true;
	}
	
	Type getType();
	
}
