package edu.harvard.seas.pl.formulog.ast.functions;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class DummyFunctionDef implements FunctionDef {

	private final Symbol sym;
	private volatile FunctionDef def;
	
	public DummyFunctionDef(Symbol sym) {
		this.sym = sym;
	}
	
	@Override
	public Symbol getSymbol() {
		return sym;
	}

	@Override
	public Term evaluate(Term[] args, Substitution substitution) throws EvaluationException {
		if (def == null) {
			throw new EvaluationException();
		}
		return def.evaluate(args, substitution);
	}
	
	public void setDef(FunctionDef def) {
		this.def = def;
	}

	public Object getDef() {
		return def;
	}

}
