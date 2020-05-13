package edu.harvard.seas.pl.formulog.smt;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import java.util.Collection;
import java.util.concurrent.ArrayBlockingQueue;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;

public class QueueSmtManager implements SmtManager {

	private final ArrayBlockingQueue<SmtLibSolver> solvers;

	public QueueSmtManager(int size) {
		if (size <= 0) {
			throw new IllegalArgumentException("Cannot have non-positive number of solvers.");
		}
		solvers = new ArrayBlockingQueue<>(size);
	}

	@Override
	public SmtResult check(Collection<SmtLibTerm> conjuncts, boolean getModel, int timeout)
			throws EvaluationException {
		SmtLibSolver solver;
		try {
			solver = solvers.take();
		} catch (InterruptedException e) {
			throw new EvaluationException(e);
		}
		SmtResult res = solver.check(conjuncts, getModel, timeout);
		solvers.add(solver);
		return res;
	}

	@Override
	public void initialize(Program<?, ?> prog) throws EvaluationException {
		while (solvers.remainingCapacity() > 0) {
			CheckSatAssumingSolver solver = new CheckSatAssumingSolver();
			solver.start(prog);
			solvers.add(solver);
		}
	}

}
