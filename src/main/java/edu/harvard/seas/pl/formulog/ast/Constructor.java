package edu.harvard.seas.pl.formulog.ast;

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface Constructor extends Functor, SmtLibTerm {

	@Override
	default <I, O> O visit(TermVisitor<I, O> v, I in) {
		return v.visit(this, in);
	}

	@Override
	default <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E {
		return v.visit(this, in);
	}

	@Override
	default Constructor applySubstitution(Substitution s) {
		Term[] newArgs = Terms.map(getArgs(), t -> t.applySubstitution(s));
		return (Constructor) copyWithNewArgs(newArgs);
	}

	@Override
	default Constructor reduce(Substitution s) throws EvaluationException {
		if (!containsFunctionCall()) {
			return this;
		}
		Term[] newArgs = Terms.mapExn(getArgs(), t -> t.reduce(s));
		return (Constructor) copyWithNewArgs(newArgs);
	}

	@Override
	Constructor copyWithNewArgs(Term[] newArgs);
	
	@Override
	default Constructor normalize(Substitution s) throws EvaluationException {
		Term[] newArgs = Terms.mapExn(getArgs(), t -> t.normalize(s));
		return (Constructor) copyWithNewArgs(newArgs);
	}
	
}
