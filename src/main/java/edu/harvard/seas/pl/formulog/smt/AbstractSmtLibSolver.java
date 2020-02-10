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

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Program;

public abstract class AbstractSmtLibSolver implements SmtLibSolver {

	private static final ExternalSolverProcessFactory solverFactory = Z3ProcessFactory.get();
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
		msg += "END SMT DECLARATIONS (SMT solver #" + hashCode() + ")";
		System.err.println(msg);
	}

	public synchronized void destroy() {
		assert solver != null;
		solver.destroy();
		solver = null;
	}
	
}
