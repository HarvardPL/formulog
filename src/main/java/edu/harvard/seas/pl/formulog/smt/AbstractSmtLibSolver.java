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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Model;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.util.Pair;

public abstract class AbstractSmtLibSolver implements SmtLibSolver {

	protected final static Pair<Collection<SolverVariable>, Collection<SolverVariable>> emptyCollectionPair = new Pair<>(
			Collections.emptyList(), Collections.emptyList());

	private static final ExternalSolverProcessFactory solverFactory;
	static {
		switch (Configuration.smtSolver) {
		case "z3":
			solverFactory = Z3ProcessFactory.get();
			break;
		case "cvc4":
			solverFactory = Cvc4ProcessFactory.get();
			break;
		case "yices":
			solverFactory = YicesProcessFactory.get();
			break;
		case "boolector":
			solverFactory = BoolectorProcessFactory.get();
			break;
		default:
			throw new AssertionError("impossible");
		}
	}
	private static final AtomicInteger solverCnt = new AtomicInteger();

	protected final int solverId = solverCnt.getAndIncrement();

	protected SmtLibShim shim;
	protected Process solver;
	private final PrintWriter log;

	protected static int taskCnt;

	public AbstractSmtLibSolver() {
		PrintWriter w = null;
		if (Configuration.debugSmt) {
			try {
				Path path = Files.createDirectories(Paths.get(Configuration.debugSmtOutDir));
				File log = path.resolve("solver" + solverId + ".log.smt2").toFile();
				w = new PrintWriter(new FileWriter(log));
			} catch (IOException e) {
				System.err.println("WARNING: Unable to create log for solver #" + solverId);
			}
		}
		log = w;
	}

	protected abstract boolean isIncremental();

	@Override
	public synchronized void start(Program<?, ?> prog) throws EvaluationException {
		assert solver == null;
		try {
			solver = solverFactory.newProcess(isIncremental());
		} catch (IOException e) {
			throw new AssertionError("Could not create external solver process:\n" + e);
		}
		BufferedReader reader = new BufferedReader(new InputStreamReader(solver.getInputStream()));
		PrintWriter writer = new PrintWriter(solver.getOutputStream());
		shim = new SmtLibShim(reader, writer, log);
		shim.initialize(prog, Configuration.smtDeclareAdts);
		start();
	}

	@Override
	public synchronized void destroy() {
		assert solver != null;
		solver.destroy();
		solver = null;
	}

	@Override
	public void finalize() {
		destroy();
	}

	protected abstract void start() throws EvaluationException;

	protected abstract Pair<Collection<SolverVariable>, Collection<SolverVariable>> makeAssertions(
			Collection<SmtLibTerm> assertions) throws EvaluationException;

	protected abstract void cleanup() throws EvaluationException;

	private SmtResult makeResult(SmtStatus status, Map<SolverVariable, Term> m, int taskId) {
		Model model = m == null ? null : Model.make(m);
		return new SmtResult(status, model, solverId, taskId);
	}

	@Override
	public synchronized SmtResult check(Collection<SmtLibTerm> assertions, boolean getModel, int timeout)
			throws EvaluationException {
		assert solver != null;
		int taskId = taskCnt++;
		if (assertions.isEmpty()) {
			Map<SolverVariable, Term> m = getModel ? Collections.emptyMap() : null;
			return makeResult(SmtStatus.SATISFIABLE, m, taskId);
		}
		String taskName = "#" + solverId + ":" + taskId + " (thread #" + Thread.currentThread().getId() + ")";
		shim.printComment("*** START CALL " + taskName + " ***");
		boolean debug = Configuration.timeSmt || log != null;
		long start = 0;
		if (debug) {
			start = System.nanoTime();
		}
		Pair<Collection<SolverVariable>, Collection<SolverVariable>> p = makeAssertions(assertions);
		long encodeTime = 0;
		if (debug) {
			long end = System.nanoTime();
			encodeTime = end - start;
			start = end;
		}
		try {
			SmtStatus status = shim.checkSatAssuming(p.fst(), p.snd(), timeout);
			if (debug) {
				long evalTime = System.nanoTime() - start;
				Configuration.recordSmtEvalTime(this, encodeTime, evalTime, status);
				if (log != null) {
					log.println("; time: " + evalTime / 1e6 + "ms");
					log.flush();
				}
			}
			Map<SolverVariable, Term> m = null;
			if (status.equals(SmtStatus.SATISFIABLE) && getModel) {
				m = shim.getModel();
			}
			cleanup();
			shim.printComment("*** END CALL " + taskName + " ***\n");
			return makeResult(status, m, taskId);
		} catch (EvaluationException e) {
			throw new EvaluationException("Problem with solver " + solverId + ":\n" + e.getMessage());
		}
	}

}
