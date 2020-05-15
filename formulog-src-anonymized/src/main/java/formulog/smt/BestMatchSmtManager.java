package formulog.smt;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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


import java.util.Collection;


import java.util.Comparator;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicIntegerArray;

import formulog.Configuration;
import formulog.ast.Program;
import formulog.ast.SmtLibTerm;
import formulog.eval.EvaluationException;
import formulog.util.Pair;

public class BestMatchSmtManager implements SmtManager {

	private final CheckSatAssumingSolver[] solvers;
	private final AtomicIntegerArray statuses;
	private static final int cacheCap = Configuration.smtCacheSize;

	public BestMatchSmtManager(int size) {
		solvers = new CheckSatAssumingSolver[size];
		statuses = new AtomicIntegerArray(size);
	}

	@Override
	public SmtResult check(Collection<SmtLibTerm> conjuncts, boolean getModel, int timeout) throws EvaluationException {
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

	private double score(Collection<SmtLibTerm> conjuncts, CheckSatAssumingSolver solver) {
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

	@Override
	public void initialize(Program<?, ?> prog) throws EvaluationException {
		for (int i = 0; i < solvers.length; ++i) {
			CheckSatAssumingSolver solver = new CheckSatAssumingSolver();
			solver.start(prog);
			solvers[i] = solver;
		}
	}

}
