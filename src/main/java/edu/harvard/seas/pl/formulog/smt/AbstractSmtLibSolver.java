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

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.SmtStatus;
import edu.harvard.seas.pl.formulog.util.Pair;

public abstract class AbstractSmtLibSolver implements SmtLibSolver {

	private static final ExternalSolverProcessFactory solverFactory = Z3ProcessFactory.get();
	private static final AtomicInteger cnt = new AtomicInteger();

	protected SmtLibShim debugShim;
	protected SmtLibShim shim;
	protected Process solver;

	public synchronized void start(Program<?, ?> prog) {
		assert solver == null;
		try {
			solver = solverFactory.newProcess();
		} catch (IOException e) {
			throw new AssertionError("Could not create external solver process:\n" + e);
		}
		BufferedReader reader = new BufferedReader(new InputStreamReader(solver.getInputStream()));
		PrintWriter writer = new PrintWriter(solver.getOutputStream());
		shim = new SmtLibShim(reader, writer, prog);
		shim.push();
		if (Configuration.debugSmt) {
			setupDebugShim(prog);
		}
	}

	private void setupDebugShim(Program<?, ?> prog) {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		debugShim = new SmtLibShim(null, new PrintWriter(baos), prog);
		String msg = "\nBEGIN SMT DECLARATIONS (SMT solver #" + hashCode() + "):\n";
		msg += baos.toString();
		msg += "(push)\n";
		msg += "END SMT DECLARATIONS (SMT solver #" + hashCode() + ")";
		System.err.println(msg);
	}

	public synchronized void destroy() {
		assert solver != null;
		solver.destroy();
		solver = null;
	}

	protected abstract Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(List<SmtLibTerm> assertions,
			int id);

	protected abstract void cleanup();

	@Override
	public synchronized Pair<SmtStatus, Map<SolverVariable, Term>> check(List<SmtLibTerm> assertions, boolean getModel,
			int timeout) throws EvaluationException {
		boolean debug = debugShim != null;
		int id = 0;
		if (debug) {
			id = cnt.getAndIncrement();
		}
		Pair<List<SolverVariable>, List<SolverVariable>> p = makeAssertions(assertions, id);
		long start = 0;
		if (debug || Configuration.timeSmt) {
			start = System.currentTimeMillis();
		}
		SmtStatus status = shim.checkSatAssuming(p.fst(), p.snd(), timeout);
		if (debug) {
			double time = (System.currentTimeMillis() - start) / 1000.0;
			System.err.println("RES SMT JOB #" + id + ": " + status + " (" + time + "s)");
		}
		if (Configuration.timeSmt) {
			long time = System.currentTimeMillis() - start;
			Configuration.recordSmtEvalTime(time);
		}
		Map<SolverVariable, Term> m = null;
		if (status.equals(SmtStatus.SATISFIABLE) && getModel) {
			m = shim.getModel();
		}
		cleanup();
		return new Pair<>(status, m);
	}

}
