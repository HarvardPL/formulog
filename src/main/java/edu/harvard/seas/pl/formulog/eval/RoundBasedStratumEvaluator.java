package edu.harvard.seas.pl.formulog.eval;

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

import java.time.LocalDateTime;
import java.util.Iterator;
import java.util.Set;

import org.apache.commons.lang3.time.StopWatch;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.db.IndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.Util;

public final class RoundBasedStratumEvaluator extends AbstractStratumEvaluator {

	volatile boolean changed;
	
	public RoundBasedStratumEvaluator(int stratumNum, SortedIndexedFactDb db,
			IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb, Iterable<IndexedRule> rules, CountingFJP exec,
			Set<RelationSymbol> trackedRelations) {
		super(stratumNum, db, deltaDbb, rules, exec, trackedRelations);
	}

	@Override
	public void evaluate() throws EvaluationException {
		int round = 0;
		StopWatch watch = recordRoundStart(round);
		for (IndexedRule r : firstRoundRules) {
			exec.externallyAddTask(new RulePrefixEvaluator(r));
		}
		exec.blockUntilFinished();
		if (exec.hasFailed()) {
			throw exec.getFailureCause();
		}
		recordRoundEnd(round, watch);
		updateDbs();
		while (changed) {
			round++;
			watch = recordRoundStart(round);
			changed = false;
			for (RelationSymbol delta : laterRoundRules.keySet()) {
				if (!deltaDb.isEmpty(delta)) {
					for (IndexedRule r : laterRoundRules.get(delta)) {
						exec.externallyAddTask(new RulePrefixEvaluator(r));
					}
				}
			}
			exec.blockUntilFinished();
			if (exec.hasFailed()) {
				throw exec.getFailureCause();
			}
			recordRoundEnd(round, watch);
			updateDbs();
		}
	}

	@Override
	protected int getSmtTaskSize() {
		return Configuration.smtTaskSize;
	}


	@Override
	void reportFact(RelationSymbol sym, Term[] args, Substitution s) throws EvaluationException {
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].normalize(s);
		}
		if (!db.hasFact(sym, newArgs) && nextDeltaDb.add(sym, newArgs)) {
			changed = true;
			if (trackedRelations.contains(sym)) {
				System.err.println("[TRACKED] " + UserPredicate.make(sym, newArgs, false));
			}
		}
	}
	
	void updateDbs() {
		StopWatch watch = recordDbUpdateStart();
		for (RelationSymbol sym : nextDeltaDb.getSymbols()) {
			if (nextDeltaDb.isEmpty(sym)) {
				continue;
			}
			Iterable<Iterable<Term[]>> answers = Util.splitIterable(nextDeltaDb.getAll(sym), taskSize);
			exec.externallyAddTask(new UpdateDbTask(sym, answers.iterator()));
		}
		exec.blockUntilFinished();
		SortedIndexedFactDb tmp = deltaDb;
		deltaDb = nextDeltaDb;
		nextDeltaDb = tmp;
		nextDeltaDb.clear();
		recordDbUpdateEnd(watch);
	}

	@SuppressWarnings("serial")
	class UpdateDbTask extends AbstractFJPTask {

		final RelationSymbol sym;
		final Iterator<Iterable<Term[]>> it;

		protected UpdateDbTask(RelationSymbol sym, Iterator<Iterable<Term[]>> it) {
			super(exec);
			this.sym = sym;
			this.it = it;
		}

		@Override
		public void doTask() throws EvaluationException {
			Iterable<Term[]> tups = it.next();
			if (it.hasNext()) {
				exec.recursivelyAddTask(new UpdateDbTask(sym, it));
			}
			db.addAll(sym, tups);
		}

	}
	
	StopWatch recordRoundStart(int round) {
		if (!Configuration.debugRounds) {
			return null;
		}
		System.err.println("#####");
		System.err.println("[START] Stratum " + stratumNum + ", round " + round);
		LocalDateTime now = LocalDateTime.now();
		System.err.println("Start: " + now);
		StopWatch watch = new StopWatch();
		watch.start();
		return watch;
	}

	void recordRoundEnd(int round, StopWatch watch) {
		if (watch == null) {
			return;
		}
		watch.stop();
		System.err.println("[END] Stratum " + stratumNum + ", round " + round);
		System.err.println("Time: " + watch.getTime() + "ms");
	}

	StopWatch recordDbUpdateStart() {
		if (!Configuration.debugRounds) {
			return null;
		}
		System.err.println("[START] Updating DBs");
		LocalDateTime now = LocalDateTime.now();
		System.err.println("Start: " + now);
		StopWatch watch = new StopWatch();
		watch.start();
		return watch;
	}

	void recordDbUpdateEnd(StopWatch watch) {
		if (watch == null) {
			return;
		}
		watch.stop();
		Configuration.printRelSizes(System.err, "DELTA SIZE", deltaDb, false);
		System.err.println("[END] Updating DBs");
		System.err.println("Time: " + watch.getTime() + "ms");
	}

}
