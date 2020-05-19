package edu.harvard.seas.pl.formulog.smt;

/*-
 * #%L
 * Formulog
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
import java.util.List;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.util.Pair;

public class SingleShotSolver extends AbstractSmtLibSolver {

	private Program<?, ?> prog;

	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(Collection<SmtLibTerm> assertions)
			throws EvaluationException {
		shim.setLogic(Configuration.smtLogic);
		shim.makeDeclarations();
		for (SmtLibTerm assertion : assertions) {
			shim.makeAssertion(assertion);
		}
		return emptyListPair;
	}

	@Override
	protected void start() throws EvaluationException {
		// do nothing
	}

	@Override
	protected void cleanup() throws EvaluationException {
		destroy();
		super.start(prog);
	}

	public synchronized void start(Program<?, ?> prog) throws EvaluationException {
		this.prog = prog;
		super.start(prog);
	}

}
