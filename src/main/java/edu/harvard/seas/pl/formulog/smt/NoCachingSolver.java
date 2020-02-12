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

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.util.Pair;

public class NoCachingSolver extends AbstractSmtLibSolver {

	private final static Pair<List<SolverVariable>, List<SolverVariable>> emptyListPair = new Pair<>(
			Collections.emptyList(), Collections.emptyList());
	
	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(List<SmtLibTerm> assertions, int id) {
		shim.pop();
		shim.push();
		ByteArrayOutputStream baos = null;
		if (debugShim != null) {
			baos = new ByteArrayOutputStream();
			debugShim.redirectOutput(new PrintWriter(baos));
			debugShim.pop();
			debugShim.push();
		}
		for (SmtLibTerm assertion : assertions) {
			shim.makeAssertion(assertion);
			if (debugShim != null) {
				debugShim.makeAssertion(assertion);
			}
		}
		if (debugShim != null) {
			String msg = "\nBEGIN SMT JOB #" + id + " (SMT solver #" + hashCode() + "):\n";
			msg += baos.toString();
			msg += "END SMT JOB #" + id;
			System.err.println(msg);
		}
		return emptyListPair;
	}

	@Override
	protected void cleanup() {
		// do nothing
	}

}
