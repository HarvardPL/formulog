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
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public final class EagerStratumEvaluator extends AbstractStratumEvaluator {

	final int stratumNum;
	final SortedIndexedFactDb db;
	final CountingFJP exec;
	final Set<RelationSymbol> trackedRelations;

	static final int taskSize = Configuration.taskSize;
	static final int smtTaskSize = 1;

	public EagerStratumEvaluator(int stratumNum, SortedIndexedFactDb db, Iterable<IndexedRule> rules, CountingFJP exec,
			Set<RelationSymbol> trackedRelations) {
		super(rules);
		this.stratumNum = stratumNum;
		this.db = db;
		this.exec = exec;
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

	void reportFact(RelationSymbol sym, Term[] args, Substitution s) throws EvaluationException {
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].normalize(s);
		}
		if (db.add(sym, newArgs)) {
			Set<IndexedRule> rs = laterRoundRules.get(sym);
			if (rs != null) {
				for (IndexedRule r : rs) {
					exec.recursivelyAddTask(new RulePrefixEvaluator(r, newArgs));
				}
			}
			if (trackedRelations.contains(sym)) {
				System.err.println("[TRACKED] " + UserPredicate.make(sym, newArgs, false));
			}
		}
	}

	Iterable<Iterable<Term[]>> lookup(IndexedRule r, int pos, OverwriteSubstitution s) throws EvaluationException {
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

	static final boolean recordRuleDiagnostics = Configuration.recordRuleDiagnostics;

	@SuppressWarnings("serial")
	class RuleSuffixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;
		final SimplePredicate head;
		final SimpleLiteral[] body;
		final int startPos;
		final OverwriteSubstitution s;
		final Iterator<Iterable<Term[]>> it;

		protected RuleSuffixEvaluator(IndexedRule rule, SimplePredicate head, SimpleLiteral[] body, int pos,
				OverwriteSubstitution s, Iterator<Iterable<Term[]>> it) {
			super(exec);
			this.rule = rule;
			this.head = head;
			this.body = body;
			this.startPos = pos;
			this.s = s;
			this.it = it;
		}

		protected RuleSuffixEvaluator(IndexedRule rule, int pos, OverwriteSubstitution s,
				Iterator<Iterable<Term[]>> it) {
			super(exec);
			this.rule = rule;
			this.head = rule.getHead();
			SimpleLiteral[] bd = new SimpleLiteral[rule.getBodySize()];
			for (int i = 0; i < bd.length; ++i) {
				bd[i] = rule.getBody(i);
			}
			this.body = bd;
			this.startPos = pos;
			this.s = s;
			this.it = it;
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			Iterable<Term[]> tups = it.next();
			if (it.hasNext()) {
				exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, head, body, startPos, s.copy(), it));
			}
			try {
				for (Term[] tup : tups) {
					evaluate(tup);
				}
			} catch (UncheckedEvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating the rule: " + rule + "\n\n" + e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRuleSuffixTime(rule, end - start);
			}
		}

		void evaluate(Term[] ans) throws UncheckedEvaluationException {
			SimplePredicate p = (SimplePredicate) body[startPos];
			updateBinding(p, ans);
			int pos = startPos + 1;
			@SuppressWarnings("unchecked")
			Iterator<Term[]>[] stack = new Iterator[rule.getBodySize()];
			boolean movingRight = true;
			while (pos > startPos) {
				if (pos == body.length) {
					try {
						reportFact(head.getSymbol(), head.getArgs(), s);
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException(
								"Exception raised while evaluating the literal: " + head + "\n\n" + e.getMessage());
					}
					pos--;
					movingRight = false;
				} else if (movingRight) {
					SimpleLiteral l = body[pos];
					try {
						switch (l.getTag()) {
						case ASSIGNMENT:
							((Assignment) l).assign(s);
							pos++;
							break;
						case CHECK:
							if (((Check) l).check(s)) {
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case DESTRUCTOR:
							if (((Destructor) l).destruct(s)) {
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case PREDICATE:
							Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s).iterator();
							if (((SimplePredicate) l).isNegated()) {
								if (!tups.hasNext()) {
									pos++;
								} else {
									pos--;
									movingRight = false;
								}
							} else {
								if (tups.hasNext()) {
									stack[pos] = tups.next().iterator();
									if (tups.hasNext()) {
										exec.recursivelyAddTask(
												new RuleSuffixEvaluator(rule, head, body, pos, s.copy(), tups));
									}
									// No need to do anything else: we'll hit the right case on the next iteration.
								} else {
									pos--;
								}
								movingRight = false;
							}
							break;
						}
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException(
								"Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
					}
				} else {
					Iterator<Term[]> it = stack[pos];
					if (it != null && it.hasNext()) {
						ans = it.next();
						updateBinding((SimplePredicate) rule.getBody(pos), ans);
						movingRight = true;
						pos++;
					} else {
						stack[pos] = null;
						pos--;
					}
				}
			}
		}

		void updateBinding(SimplePredicate p, Term[] ans) {
			Term[] args = p.getArgs();
			BindingType[] pat = p.getBindingPattern();
			for (int i = 0; i < pat.length; ++i) {
				if (pat[i].isFree()) {
					s.put((Var) args[i], ans[i]);
				}
			}
		}

	}

	@SuppressWarnings("serial")
	class RulePrefixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;
		final Term[] deltaArgs;

		protected RulePrefixEvaluator(IndexedRule rule, Term[] deltaArgs) {
			super(exec);
			this.rule = rule;
			this.deltaArgs = deltaArgs;
		}

		private boolean handleDelta(SimplePredicate pred, Substitution s) throws EvaluationException {
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
			return true;
		}

		@Override
		public void doTask() throws EvaluationException {
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

		void evaluate() throws EvaluationException {
			int len = rule.getBodySize();
			int pos = 0;
			OverwriteSubstitution s = new OverwriteSubstitution();
			loop: for (; pos < len; ++pos) {
				SimpleLiteral l = rule.getBody(pos);
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
			if (pos == len) {
				try {
					SimplePredicate head = rule.getHead();
					reportFact(head.getSymbol(), head.getArgs(), s);
					return;
				} catch (EvaluationException e) {
					throw new EvaluationException("Exception raised while evaluationg the literal: "
							+ rule.getHead() + e.getLocalizedMessage());
				}
			}
			Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s).iterator();
			if (tups.hasNext()) {
				exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, pos, s, tups));
			}
		}
	}

}
