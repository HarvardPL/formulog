package edu.harvard.seas.pl.formulog.unification;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;

public interface Substitution {
	
	void put(Var v, Term t);
	
	Term get(Var v);

	static Term getIfPresent(Term t, Substitution s) {
		if (t instanceof Var && s.containsKey((Var) t)) {
			return s.get((Var) t);
		}
		return t;
	}
	
	boolean containsKey(Var v);
	
	Iterable<Var> iterateKeys();

//	Substitution copy();
	
//	int newCheckpoint();

//	int getCheckpoint();

//	void revertTo(int checkpoint);

//	int popCheckpoint();

//	void mergeCheckpoint();
	
}
