package edu.harvard.seas.pl.formulog.eval;

/*-
 * #%L
 * Formulog
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

import java.util.Iterator;
import java.util.Set;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.OverwriteSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.SharedLong;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public final class EagerStratumEvaluator extends AbstractStratumEvaluator {

	private final SortedIndexedFactDb db;
	private final Set<RelationSymbol> trackedRelations;

	static final int taskSize = Configuration.taskSize;
	static final int smtTaskSize = 1;

	public EagerStratumEvaluator(SortedIndexedFactDb db, Iterable<IndexedRule> rules, CountingFJP exec,
			Set<RelationSymbol> trackedRelations) {
		super(rules, exec);
		this.db = db;
		this.trackedRelations = trackedRelations;
	}

	@Override
	public void evaluate() throws EvaluationException {
		for (IndexedRule r : firstRoundRules) {
			exec.externallyAddTask(new RulePrefixEvaluator(r, null));
		}
		exec.blockUntilFinished();
		if (exec.hasFailed()) {
			throw exec.getFailureCause();
		}
	}

	@Override
	protected void reportFact(RelationSymbol sym, Term[] args) {
		Term[] copy = args.clone();
		if (db.add(sym, copy)) {
			Set<IndexedRule> rs = laterRoundRules.get(sym);
			if (rs != null) {
				for (IndexedRule r : rs) {
					exec.recursivelyAddTask(new RulePrefixEvaluator(r, copy));
				}
			}
			if (trackedRelations.contains(sym)) {
				System.err.println("[TRACKED] " + UserPredicate.make(sym, copy, false));
			}
			if (Configuration.recordDetailedWork) {
				Configuration.newDerivs.increment();
			}
		} else if (Configuration.recordDetailedWork) {
			Configuration.dupDerivs.increment();
		}
	}

	@Override
	protected boolean checkFact(RelationSymbol sym, Term[] args, Substitution s, Term[] scratch)
			throws EvaluationException {
		for (int i = 0; i < args.length; ++i) {
			scratch[i] = args[i].normalize(s);
		}
		return !db.hasFact(sym, scratch);
	}

	@Override
	protected Iterable<Iterable<Term[]>> lookup(IndexedRule r, int pos, OverwriteSubstitution s)
			throws EvaluationException {
		SimplePredicate predicate = (SimplePredicate) r.getBody(pos);
		int idx = r.getDbIndex(pos);
		Term[] args = predicate.getArgs();
		Term[] key = new Term[args.length];
		BindingType[] pat = predicate.getBindingPattern();
		for (int i = 0; i < args.length; ++i) {
			if (pat[i].isBound()) {
				key[i] = args[i].normalize(s);
			} else {
				key[i] = args[i];
			}
		}
		RelationSymbol sym = predicate.getSymbol();
		assert !(sym instanceof DeltaSymbol);
		Iterable<Term[]> ans = db.get(sym, key, idx);
		boolean shouldSplit = splitPositions.get(r)[pos];
		int targetSize = shouldSplit ? smtTaskSize : taskSize;
		return Util.splitIterable(ans, targetSize);
	}

	@SuppressWarnings("serial")
	private class RulePrefixEvaluator extends AbstractFJPTask {

		private final IndexedRule rule;
		private final Term[] deltaArgs;

		protected RulePrefixEvaluator(IndexedRule rule, Term[] deltaArgs) {
			super(exec);
			this.rule = rule;
			this.deltaArgs = deltaArgs;
			if (Configuration.recordDetailedWork) {
				Configuration.workItems.increment();
			}
		}

		private final boolean handleDelta(SimplePredicate pred, Substitution s) throws EvaluationException {
			BindingType[] bindings = pred.getBindingPattern();
			Term[] args = pred.getArgs();
			int i = 0;
			for (BindingType b : bindings) {
				Term arg = args[i];
				if (b.isFree()) {
					assert arg instanceof Var;
					s.put((Var) arg, deltaArgs[i]);
				} else if (b.isBound()) {
					if (!arg.normalize(s).equals(deltaArgs[i])) {
						return false;
					}
				}
				++i;
			}
			if (Configuration.recordWork) {
				Configuration.work.increment();
			}
			if (Configuration.recordDetailedWork) {
				Util.lookupOrCreate(Configuration.workPerRule, rule, SharedLong::new).increment();
			}
			return true;
		}

		@Override
		public final void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			try {
				evaluate();
			} catch (EvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating the rule:\n" + rule + "\n\n" + e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRulePrefixTime(rule, end - start);
			}
		}

		private void evaluate() throws EvaluationException {
			int len = rule.getBodySize();
			int pos = 0;
			OverwriteSubstitution s = new OverwriteSubstitution();
			SimplePredicate head = rule.getHead();
			var scratch = new Term[head.getSymbol().getArity()];
			var checkPos = checkPosition.get(rule);
			loop: for (; pos <= len; ++pos) {
				SimpleLiteral l = head;
				if (checkPos == pos && !checkFact(head.getSymbol(), head.getArgs(), s, scratch)) {
					return;
				}
				if (pos == len) {
					reportFact(head.getSymbol(), scratch);
					return;
				}
				l = rule.getBody(pos);
				try {
					switch (l.getTag()) {
					case ASSIGNMENT:
						((Assignment) l).assign(s);
						break;
					case CHECK:
						if (!((Check) l).check(s)) {
							return;
						}
						break;
					case DESTRUCTOR:
						if (!((Destructor) l).destruct(s)) {
							return;
						}
						break;
					case PREDICATE:
						SimplePredicate p = (SimplePredicate) l;
						if (p.isNegated()) {
							if (lookup(rule, pos, s).iterator().hasNext()) {
								return;
							}
						} else {
							RelationSymbol sym = p.getSymbol();
							if (!(sym instanceof DeltaSymbol)) {
								break loop;
							}
							if (!handleDelta(p, s)) {
								return;
							}
						}
						break;
					}
				} catch (EvaluationException e) {
					throw new EvaluationException(
							"Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
				}
			}
			Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s).iterator();
			if (tups.hasNext()) {
				new RuleSuffixEvaluator(rule, pos, s, tups, scratch.clone()).doTask();
			}
		}
	}

}
