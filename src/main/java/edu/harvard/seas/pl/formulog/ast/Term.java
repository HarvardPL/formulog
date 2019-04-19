package edu.harvard.seas.pl.formulog.ast;

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface Term {
	
	<I, O> O visit(TermVisitor<I, O> v, I in);
	
	<I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E;
	
	boolean isGround();

	boolean containsFunctionCall();

	Term applySubstitution(Substitution s);
	
	Term reduce(Substitution s) throws EvaluationException;
	
	Term normalize(Substitution s) throws EvaluationException;
	
}
