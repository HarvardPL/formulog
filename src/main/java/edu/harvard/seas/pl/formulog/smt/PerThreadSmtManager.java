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

import java.util.Map;
import java.util.function.Supplier;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.util.Pair;

public class PerThreadSmtManager extends SmtManager {

	private final ThreadLocal<SmtManager> subManager;
	
	public PerThreadSmtManager(Supplier<SmtManager> managerMaker) {
		subManager = new ThreadLocal<SmtManager>() {
		
			@Override
			protected SmtManager initialValue() {
				return managerMaker.get();
			}
			
		};
	}
	
	@Override
	public Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm assertion, int timeout) throws EvaluationException {
		return subManager.get().check(assertion, timeout);
	}

}
