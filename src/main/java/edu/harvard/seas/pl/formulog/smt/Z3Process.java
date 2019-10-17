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
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.util.Pair;

public class Z3Process {

	static {
		String os = System.getProperty("os.name");
		String cmd = "";
		if (os.startsWith("Windows")) {
			cmd += "where";
		} else {
			cmd += "which";
		}
		cmd += " z3";
		try {
			Process p = Runtime.getRuntime().exec(cmd);
			if (p.waitFor() != 0) {
				throw new AssertionError(
						"Cannot find z3 executable on path (`" + cmd + "` returned a non-zero exit code).");
			}
		} catch (IOException | InterruptedException e) {
			throw new AssertionError("Command checking for presence of z3 executable failed: " + cmd);
		}
	}

	private static final AtomicInteger cnt = new AtomicInteger();
	private SmtLibShim debugShim;
	private SmtLibShim shim;
	private Process z3;

	public synchronized void start(Program<?, ?> prog) {
		assert z3 == null;
		try {
			z3 = Runtime.getRuntime().exec("z3 -in -smt2");
			BufferedReader reader = new BufferedReader(new InputStreamReader(z3.getInputStream()));
			PrintWriter writer = new PrintWriter(z3.getOutputStream());
			shim = new SmtLibShim(reader, writer, prog.getSymbolManager());
			shim.makeDeclarations(prog);
			if (Configuration.debugSmt) {
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				debugShim = new SmtLibShim(reader, new PrintWriter(baos), prog.getSymbolManager());
				String msg = "\nBEGIN Z3 DECLARATIONS (Z3Process " + this + "):\n";
				msg += baos.toString();
				msg += "\nEND Z3 DECLARATIONS (Z3Process " + this + ")";
				System.err.println(msg);
			}
		} catch (IOException e) {
			throw new RuntimeException("Could not run Z3:\n" + e);
		}
	}
	
	public synchronized void destroy() {
		assert z3 != null;
		z3.destroy();
		z3 = null;
	}

	private void makeAssertion(SmtLibTerm formula, Integer id) {
		if (debugShim != null) {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			debugShim.redirectOutput(new PrintWriter(baos));
			debugShim.push();
			debugShim.makeAssertion(formula);
			debugShim.pop();
			String msg = "\nBEGIN Z3 JOB #" + id + " (Z3Process " + this + "):\n";
			msg += baos.toString();
			msg += "\nEND Z3 JOB #" + id;
			System.err.println(msg);
		}
		shim.makeAssertion(formula);
	}

	public synchronized Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm t, Integer timeout) throws EvaluationException {
		boolean debug = debugShim != null;
		int id = 0;
		if (debug) {
			id = cnt.getAndIncrement();
		}
		shim.push();
		makeAssertion(t, id);
		long start = 0;
		if (debug || Configuration.timeSmt) {
			start = System.currentTimeMillis();
		}
		Status status = shim.checkSat(timeout);
		if (debug) {
			double time = (System.currentTimeMillis() - start) / 1000.0;
			System.err.println("\nRES Z3 JOB #" + id + ": " + status + " (" + time + "s)");
		}
		if (Configuration.timeSmt) {
			long time = System.currentTimeMillis() - start;
			Configuration.recordSmtEvalTime(time);
		}
		Map<SolverVariable, Term> m = null;
		if (status.equals(Status.SATISFIABLE)) {
			m = shim.getModel();
		}
		shim.pop();
		return new Pair<>(status, m);
	}

}
