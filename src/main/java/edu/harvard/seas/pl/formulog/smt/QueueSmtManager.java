package edu.harvard.seas.pl.formulog.smt;

import java.util.List;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

import java.util.Map;
import java.util.concurrent.ArrayBlockingQueue;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.util.Pair;

public class QueueSmtManager extends AbstractSmtManager {

	private final ArrayBlockingQueue<Z3Process> processes;

	public QueueSmtManager(Program<UserPredicate, BasicRule> prog, int size) {
		processes = new ArrayBlockingQueue<>(size);
		for (int i = 0; i < size; ++i) {
			Z3Process proc = new Z3Process();
			proc.start(prog);
			processes.add(proc);
		}
	}

	@Override
	public Pair<Status, Map<SolverVariable, Term>> check(List<SmtLibTerm> conjuncts, boolean getModel, int timeout)
			throws EvaluationException {
		Z3Process proc;
		try {
			proc = processes.take();
		} catch (InterruptedException e) {
			throw new EvaluationException(e);
		}
		Pair<Status, Map<SolverVariable, Term>> res = proc.check(conjuncts, getModel, timeout);
		processes.add(proc);
		return res;
	}

}
