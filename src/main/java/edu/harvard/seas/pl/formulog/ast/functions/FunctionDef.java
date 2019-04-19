package edu.harvard.seas.pl.formulog.ast.functions;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.EmptySubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface FunctionDef {

	Symbol getSymbol();
	
	Term evaluate(Term[] args, Substitution substitution) throws EvaluationException;
	
	default Term evaluate(Term[] args) throws EvaluationException {
		return evaluate(args, EmptySubstitution.INSTANCE);
	}
}
