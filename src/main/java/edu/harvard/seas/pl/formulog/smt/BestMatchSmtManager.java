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
import java.util.concurrent.atomic.AtomicIntegerArray;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.SmtStatus;
import edu.harvard.seas.pl.formulog.util.Pair;

public class BestMatchSmtManager extends AbstractSmtManager {

	private final CheckSatAssumingSolver[] solvers;
	private final AtomicIntegerArray statuses;
	private static final int cacheCap = Configuration.smtCacheSize;

	public BestMatchSmtManager(Program<?, ?> prog, int size) {
		solvers = new CheckSatAssumingSolver[size];
		statuses = new AtomicIntegerArray(size);
		for (int i = 0; i < size; ++i) {
			CheckSatAssumingSolver solver = new CheckSatAssumingSolver();
			solver.start(prog);
			solvers[i] = solver;
		}
	}

	@Override
	public Pair<SmtStatus, Map<SolverVariable, Term>> check(List<SmtLibTerm> conjuncts, boolean getModel, int timeout)
			throws EvaluationException {
		while (true) {
			PriorityQueue<Pair<Integer, Double>> q = new PriorityQueue<>(solvers.length, cmp);
			for (int i = 0; i < solvers.length; ++i) {
				double score = score(conjuncts, solvers[i]);
				q.add(new Pair<>(i, score));
			}
			while (!q.isEmpty()) {
				int i = q.remove().fst();
				if (statuses.compareAndSet(i, 0, 1)) {
					try {
						return solvers[i].check(conjuncts, getModel, timeout);
					} finally {
						statuses.set(i, 0);
					}
				}
			}
		}
	}

	private static final Comparator<Pair<Integer, Double>> cmp = new Comparator<Pair<Integer, Double>>() {

		@Override
		public int compare(Pair<Integer, Double> o1, Pair<Integer, Double> o2) {
			return Double.compare(o2.snd(), o1.snd());
		}

	};

	private double score(List<SmtLibTerm> conjuncts, CheckSatAssumingSolver solver) {
		Set<SmtLibTerm> cache = solver.getCache();
		int cacheSize = cache.size();
		if (cacheSize == 0) {
			return 0;
		}
		int hits = 0;
		for (SmtLibTerm conjunct : conjuncts) {
			if (cache.contains(conjunct)) {
				hits++;
			}
		}
		double score1 = 3 * hits / conjuncts.size();
		double score2 = -((cacheSize - hits) / cacheCap);
		return score1 + score2;
	}

}
