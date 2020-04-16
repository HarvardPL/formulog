package edu.harvard.seas.pl.formulog.smt;

import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.SmtStatus;
import edu.harvard.seas.pl.formulog.util.Pair;

public class NotThreadSafeQueueSmtManager extends AbstractSmtManager {

	private final SmtLibSolver[] solvers;
	private int pos;

	public NotThreadSafeQueueSmtManager(Program<UserPredicate, BasicRule> prog, int size) {
		if (size <= 0) {
			throw new IllegalArgumentException("Cannot have non-positive number of solvers.");
		}
		solvers = new SmtLibSolver[size];
		for (int i = 0; i < size; ++i) {
			CheckSatAssumingSolver solver = new CheckSatAssumingSolver();
			solver.start(prog);
			solvers[i] = solver;
		}
	}

	@Override
	public Pair<SmtStatus, Map<SolverVariable, Term>> check(List<SmtLibTerm> conjuncts, boolean getModel, int timeout)
			throws EvaluationException {
		SmtLibSolver solver = solvers[pos];
		Pair<SmtStatus, Map<SolverVariable, Term>> res = solver.check(conjuncts, getModel, timeout);
		pos = (pos + 1) % solvers.length;
		return res;
	}
}
