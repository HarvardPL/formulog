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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
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

public abstract class AbstractStratumEvaluator implements StratumEvaluator {

	protected final Set<IndexedRule> firstRoundRules = new HashSet<>();
	protected final Map<RelationSymbol, Set<IndexedRule>> laterRoundRules = new HashMap<>();
	protected final Map<IndexedRule, boolean[]> splitPositions = new HashMap<>();
	protected final Map<IndexedRule, Integer> checkPosition = new HashMap<>();
	protected final CountingFJP exec;

	public AbstractStratumEvaluator(Iterable<IndexedRule> rules, CountingFJP exec) {
		processRules(rules);
		this.exec = exec;
	}

	private void processRules(Iterable<IndexedRule> rules) {
		SmtCallFinder scf = new SmtCallFinder();
		for (IndexedRule rule : rules) {
			RelationSymbol delta = EvalUtil.findDelta(rule);
			if (delta != null) {
				Util.lookupOrCreate(laterRoundRules, delta, () -> new HashSet<>()).add(rule);
			} else {
				firstRoundRules.add(rule);
			}
			boolean[] positions = findSplitPositions(rule, scf);
			splitPositions.put(rule, positions);
			checkPosition.put(rule, findCheckPosition(rule));
		}
	}

	private static boolean[] findSplitPositions(IndexedRule rule, SmtCallFinder scf) {
		int len = rule.getBodySize();
		boolean[] splitPositions = new boolean[len];
		boolean smtCallComing = scf.containsSmtCall(rule.getHead());
		for (int i = len - 1; i >= 0; --i) {
			SimpleLiteral l = rule.getBody(i);
			if (smtCallComing && l instanceof SimplePredicate && !((SimplePredicate) l).isNegated()) {
				splitPositions[i] = true;
				smtCallComing = scf.containsSmtCall(l);
			} else {
				smtCallComing = smtCallComing || scf.containsSmtCall(l);
			}
		}
		return splitPositions;
	}

	private static int findCheckPosition(IndexedRule rule) {
		var headVars = rule.getHead().varSet();
		Set<Var> bound = new HashSet<>();
		int i = 0;
		for (; i < rule.getBodySize(); ++i) {
			if (bound.containsAll(headVars)) {
				break;
			}
			rule.getBody(i).varSet(bound);
		}
		return i;
	}

	abstract protected void reportFact(RelationSymbol sym, Term[] args);

	abstract protected boolean checkFact(RelationSymbol sym, Term[] args, Substitution s, Term[] scratch)
			throws EvaluationException;

	abstract protected Iterable<Iterable<Term[]>> lookup(IndexedRule r, int pos, OverwriteSubstitution s)
			throws EvaluationException;

	protected static final boolean recordRuleDiagnostics = Configuration.recordRuleDiagnostics;

	@SuppressWarnings("serial")
	protected class RuleSuffixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;
		final SimplePredicate head;
		final SimpleLiteral[] body;
		final int startPos;
		final OverwriteSubstitution s;
		final Iterator<Iterable<Term[]>> it;
		final Term[] scratch;

		protected RuleSuffixEvaluator(IndexedRule rule, SimplePredicate head, SimpleLiteral[] body, int pos,
				OverwriteSubstitution s, Iterator<Iterable<Term[]>> it, Term[] scratch) {
			super(exec);
			this.rule = rule;
			this.head = head;
			this.body = body;
			this.startPos = pos;
			this.s = s;
			this.it = it;
			this.scratch = scratch;
			if (Configuration.recordDetailedWork) {
				Configuration.workItems.increment();
			}
		}

		protected RuleSuffixEvaluator(IndexedRule rule, int pos, OverwriteSubstitution s, Iterator<Iterable<Term[]>> it,
				Term[] scratch) {
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
			this.scratch = scratch;
			if (Configuration.recordDetailedWork) {
				Configuration.workItems.increment();
			}
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			Iterable<Term[]> tups = it.next();
			if (it.hasNext()) {
				exec.recursivelyAddTask(
						new RuleSuffixEvaluator(rule, head, body, startPos, s.copy(), it, scratch.clone()));
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

		private void evaluate(Term[] ans) throws UncheckedEvaluationException {
			SimplePredicate p = (SimplePredicate) body[startPos];
			updateBinding(p, ans);
			int pos = startPos + 1;
			@SuppressWarnings("unchecked")
			Iterator<Term[]>[] stack = new Iterator[rule.getBodySize()];
			boolean movingRight = true;
			var checkPos = checkPosition.get(rule);
			while (pos > startPos) {
				try {
					if (movingRight && checkPos == pos && !checkFact(head.getSymbol(), head.getArgs(), s, scratch)) {
						pos--;
						movingRight = false;
					}
				} catch (EvaluationException e) {
					throw new UncheckedEvaluationException(
							"Exception raised while evaluating the literal: " + head + "\n\n" + e.getMessage());
				}
				if (pos == body.length) {
					reportFact(head.getSymbol(), scratch);
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
										exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, head, body, pos, s.copy(),
												tups, scratch.clone()));
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

		private void updateBinding(SimplePredicate p, Term[] ans) {
			if (Configuration.recordWork) {
				Configuration.work.increment();
			}
			Term[] args = p.getArgs();
			BindingType[] pat = p.getBindingPattern();
			for (int i = 0; i < pat.length; ++i) {
				if (pat[i].isFree()) {
					s.put((Var) args[i], ans[i]);
				}
			}
		}

	}

}
