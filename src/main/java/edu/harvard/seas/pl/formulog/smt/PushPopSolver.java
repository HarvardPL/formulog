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
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.util.Pair;

public class PushPopSolver extends AbstractSmtLibSolver {

	private final Deque<SmtLibTerm> cache = new ArrayDeque<>();

	private final static Pair<List<SolverVariable>, List<SolverVariable>> emptyListPair = new Pair<>(
			Collections.emptyList(), Collections.emptyList());

	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(List<SmtLibTerm> assertions, int id) {
		ByteArrayOutputStream baos = null;
		if (debugShim != null) {
			baos = new ByteArrayOutputStream();
			debugShim.redirectOutput(new PrintWriter(baos));
		}
		int i = findDiffPos(assertions);
		shrinkCache(i);
		growCache(assertions.listIterator(i));
		if (debugShim != null) {
			String msg = "\nBEGIN SMT JOB #" + id + " (SMT solver #" + hashCode() + "):\n";
			msg += baos.toString();
			msg += "END SMT JOB #" + id;
			System.err.println(msg);
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

	private void shrinkCache(int tgtSize) {
		int size = cache.size();
		while (size > tgtSize) {
			shim.pop();
			if (debugShim != null) {
				debugShim.pop();
			}
			cache.removeLast();
			--size;
		}
	}
	
	private void growCache(Iterator<SmtLibTerm> assertions) {
		while (assertions.hasNext()) {
			SmtLibTerm assertion = assertions.next();
			shim.push();
			shim.makeAssertion(assertion);
			if (debugShim != null) {
				debugShim.push();
				debugShim.makeAssertion(assertion);
			}
			cache.addLast(assertion);
		}
	}

	@Override
	protected void cleanup() {
		// Do nothing
	}

}
