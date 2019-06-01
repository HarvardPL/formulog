package edu.harvard.seas.pl.formulog.ast.functions;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.ast.functions.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface Expr extends Term {

	<I, O> O visit(ExprVisitor<I, O> visitor, I in);

	<I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E;

	@Override
	default <I, O> O visit(TermVisitor<I, O> visitor, I in) {
		return visitor.visit(this, in);
	}
	
	@Override
	default <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> visitor, I in) throws E {
		return visitor.visit(this, in);
	}
	
	@Override
	default boolean containsFunctionCall() {
		return true;
	}
	
	@Override
	default Term reduce(Substitution s) throws EvaluationException {
		return normalize(s);
	}
	
	@Override
	default boolean isGround() {
		return Terms.varSet(this).isEmpty();
	}

}