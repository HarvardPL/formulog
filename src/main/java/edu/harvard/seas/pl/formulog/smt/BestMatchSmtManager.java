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

import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicIntegerArray;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.util.Pair;

public class BestMatchSmtManager extends SmtManager {

	private final Z3Process[] processes;
	private final AtomicIntegerArray statuses;
	private int cnt = 0;

	public BestMatchSmtManager(Program<?, ?> prog, int size) {
		processes = new Z3Process[size];
		statuses = new AtomicIntegerArray(size);
		for (int i = 0; i < size; ++i) {
			Z3Process proc = new Z3Process();
			proc.start(prog);
			processes[i] = proc;
		}
	}

	@Override
	public Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm assertion, int timeout) throws EvaluationException {
		List<SmtLibTerm> conjuncts = breakIntoConjuncts(assertion);
		while (true) {
			PriorityQueue<Pair<Integer, Integer>> q = new PriorityQueue<>(processes.length, cmp);
			// This is intentionally non-synchronized.
			int start = cnt++;
			for (int i = 0; i < processes.length; ++i) {
				int pos = (start + i) % processes.length;
				int score = score(conjuncts, processes[pos]);
				q.add(new Pair<>(i, score));
			}
			while (!q.isEmpty()) {
				int i = q.remove().fst();
				if (statuses.compareAndSet(i, 0, 1)) {
					try {
						return processes[i].check(conjuncts, timeout);
					} finally {
						statuses.set(i, 0);
					}
				}
			}
		}
	}

	private static final Comparator<Pair<Integer, Integer>> cmp = new Comparator<Pair<Integer, Integer>>() {

		@Override
		public int compare(Pair<Integer, Integer> o1, Pair<Integer, Integer> o2) {
			return -Integer.compare(o1.snd(), o2.snd());
		}

	};

	private int score(List<SmtLibTerm> conjuncts, Z3Process proc) {
		Set<SmtLibTerm> cache = proc.getCache();
		int score = 0;
		for (SmtLibTerm conjunct : conjuncts) {
			if (cache.contains(conjunct)) {
				score++;
			}
		}
		return score;
	}

}
