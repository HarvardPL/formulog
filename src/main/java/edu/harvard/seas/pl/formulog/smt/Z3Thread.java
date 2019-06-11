package edu.harvard.seas.pl.formulog.smt;

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

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Map;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinWorkerThread;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.util.Pair;

public class Z3Thread extends ForkJoinWorkerThread {

	private final boolean debug = System.getProperty("debugSmt") != null;
	private final AtomicInteger cnt = new AtomicInteger();
	private final SymbolManager symbolManager;

	private Process z3;

	protected Z3Thread(ForkJoinPool pool, SymbolManager symbolManager) {
		super(pool);
		this.symbolManager = symbolManager;
	}

	@Override
	protected synchronized void onStart() {
		try {
			z3 = Runtime.getRuntime().exec("z3 -in -smt2");
		} catch (IOException e) {
			e.printStackTrace();
			throw new AssertionError();
		}
	}

	@Override
	protected synchronized void onTermination(Throwable exception) {
		z3.destroy();
	}

	private SmtLibShim makeAssertion(SmtLibTerm formula, Integer id) {
		BufferedReader reader = new BufferedReader(new InputStreamReader(z3.getInputStream()));
		PrintWriter writer;
		if (debug) {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			writer = new PrintWriter(baos);
			SmtLibShim shim = new SmtLibShim(reader, writer, symbolManager);
			shim.reset();
			shim.makeAssertion(formula);
			String msg = "\nBEGIN Z3 JOB #" + id + " (THREAD " + Thread.currentThread().getName() + "):\n";
			msg += baos.toString();
			msg += "\nEND Z3 JOB #" + id;
			System.err.println(msg);
		}
		writer = new PrintWriter(z3.getOutputStream());
		SmtLibShim shim = new SmtLibShim(reader, writer, symbolManager);
		shim.reset();
		shim.makeAssertion(formula);
		return shim;
	}

	public Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm t, Integer timeout) throws EvaluationException {
		t = (new SmtLibSimplifier()).simplify(t);
		Integer id = null;
		if (debug) {
			id = cnt.getAndIncrement();
		}
		SmtLibShim shim = makeAssertion(t, id);
		Status status = shim.checkSat(timeout);
		if (debug) {
			System.err.println("\nRES Z3 JOB #" + id + ": " + status);
		}
		Map<SolverVariable, Term> m = null;
		if (status.equals(Status.SATISFIABLE)) {
			m = shim.getModel();
		}
		return new Pair<>(status, m);
	}

}
