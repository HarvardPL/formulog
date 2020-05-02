package edu.harvard.seas.pl.formulog.smt;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.util.Pair;

public class PushPopSolver extends AbstractSmtLibSolver {

	private final Deque<SmtLibTerm> cache = new ArrayDeque<>();

	private final static Pair<List<SolverVariable>, List<SolverVariable>> emptyListPair = new Pair<>(
			Collections.emptyList(), Collections.emptyList());

	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(List<SmtLibTerm> assertions)
			throws EvaluationException {
		int baseSize = cache.size();
		int i = findDiffPos(assertions);
		int pops = baseSize - i;
		shrinkCache(i);
		growCache(assertions.listIterator(i));
		if (Configuration.timeSmt) {
			Configuration.recordPushPopSolverStats(solverId, baseSize, pops, cache.size() - i);
		}
		return emptyListPair;
	}

	private int findDiffPos(List<SmtLibTerm> assertions) {
		int i = 0;
		Iterator<SmtLibTerm> cacheIt = cache.iterator();
		for (SmtLibTerm assertion : assertions) {
			if (!cacheIt.hasNext()) {
				break;
			}
			SmtLibTerm cached = cacheIt.next();
			if (!cached.equals(assertion)) {
				break;
			}
			++i;
		}
		return i;
	}

	private void shrinkCache(int tgtSize) throws EvaluationException {
		int size = cache.size();
		while (size > tgtSize) {
			shim.pop();
			cache.removeLast();
			--size;
		}
	}

	private void growCache(Iterator<SmtLibTerm> assertions) throws EvaluationException {
		while (assertions.hasNext()) {
			SmtLibTerm assertion = assertions.next();
			shim.push();
			shim.makeAssertion(assertion);
			cache.addLast(assertion);
		}
	}

	@Override
	protected void cleanup() {
		// Do nothing
	}

	@Override
	protected void start() throws EvaluationException {
		shim.setLogic(Configuration.smtLogic);
		shim.makeDeclarations();
	}

}
