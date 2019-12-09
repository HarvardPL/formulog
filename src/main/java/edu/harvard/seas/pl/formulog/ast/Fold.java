package edu.harvard.seas.pl.formulog.ast;

import java.util.Arrays;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class Fold implements Expr {

	private final FunctionSymbol f;
	private final Term[] args;
	private final FunctionCallFactory funCalls;
	private Boolean isGround;

	public Fold(FunctionSymbol f, Term[] args, FunctionCallFactory funCalls) {
		this.f = f;
		this.args = args;
		this.funCalls = funCalls;
		if (f.getArity() != args.length) {
			throw new IllegalArgumentException("Arity mismatch when defining fold over " + f + " (it needs "
					+ f.getArity() + " arguments, but got the arguments " + Arrays.toString(args) + ").");
		}
	}
	
	public Term[] getArgs() {
		return args;
	}
	
	public FunctionSymbol getFunction() {
		return f;
	}
	
	public FunctionCall getRepresentativeCall() {
		return funCalls.make(f, args);
	}

	@Override
	public boolean isGround() {
		if (isGround != null) {
			return isGround;
		}
		for (Term arg : args) {
			if (!arg.isGround()) {
				return (isGround = false);
			}
		}
		return (isGround = true);
	}

	@Override
	public Term applySubstitution(Substitution s) {
		return new Fold(f, applySubstitutionToArgs(s), funCalls);
	}
	
	private Term[] applySubstitutionToArgs(Substitution s) {
		Term[] newArgs = new Term[args.length];
		int i = 0;
		for (Term arg : args) {
			newArgs[i] = arg.applySubstitution(s);
			i++;
		}
		return newArgs;
	}

	@Override
	public Term normalize(Substitution s) throws EvaluationException {
		Term[] args = applySubstitutionToArgs(s);
		Term acc = args[0];
		Constructor list = (Constructor) args[1];
		FunctionDef def = funCalls.getDefManager().lookup(f);
		while (list.getSymbol().equals(BuiltInConstructorSymbol.CONS)) {
			Term[] consCell = list.getArgs();
			Term head = consCell[0];
			list = (Constructor) consCell[1];
			args[0] = acc;
			args[1] = head;
			acc = def.evaluate(args);
		}
		return acc;
	}

	@Override
	public void varSet(Set<Var> acc) {
		for (Term arg : args) {
			arg.varSet(acc);
		}
	}

	@Override
	public void updateVarCounts(Map<Var, Integer> counts) {
		for (Term arg : args) {
			arg.updateVarCounts(counts);
		}
	}

	@Override
	public int getId() {
		throw new UnsupportedOperationException();
	}

	@Override
	public <I, O> O accept(ExprVisitor<I, O> visitor, I in) {
		return visitor.visit(this, in);
	}

	@Override
	public <I, O, E extends Throwable> O accept(ExprVisitorExn<I, O, E> visitor, I in) throws E {
		return visitor.visit(this, in);
	}

}
