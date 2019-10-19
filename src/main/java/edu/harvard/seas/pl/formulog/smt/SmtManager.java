package edu.harvard.seas.pl.formulog.smt;

import java.util.ArrayList;
import java.util.Collections;
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

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

public class SmtManager {

	private final ArrayBlockingQueue<Z3Process> processes;

	public SmtManager(Program<UserPredicate, BasicRule> prog) {
		int size = Configuration.smtParallelism;
		processes = new ArrayBlockingQueue<>(size);
		for (int i = 0; i < size; ++i) {
			Z3Process proc = new Z3Process();
			proc.start(prog);
			processes.add(proc);
		}
	}

	public Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm assertion, int timeout) throws EvaluationException {
		Z3Process proc;
		try {
			proc = processes.take();
		} catch (InterruptedException e) {
			throw new EvaluationException(e);
		}
		Pair<Status, Map<SolverVariable, Term>> res = proc.check(breakIntoConjuncts(assertion), timeout);
		processes.add(proc);
		return res;
	}

	private List<SmtLibTerm> breakIntoConjuncts(SmtLibTerm assertion) {
		List<SmtLibTerm> l = new ArrayList<>();
		breakIntoConjuncts(assertion, l);
		return l;
	}
	
	private void breakIntoConjuncts(SmtLibTerm assertion, List<SmtLibTerm> acc) {
		Constructor c = (Constructor) assertion;
		ConstructorSymbol sym = c.getSymbol();
		Term[] args = c.getArgs();
		if (sym.equals(BuiltInConstructorSymbol.FORMULA_AND)) {
			breakIntoConjuncts((SmtLibTerm) args[0], acc);
			breakIntoConjuncts((SmtLibTerm) args[1], acc);
		} else {
			acc.add(assertion);
		}
	}
	
}
