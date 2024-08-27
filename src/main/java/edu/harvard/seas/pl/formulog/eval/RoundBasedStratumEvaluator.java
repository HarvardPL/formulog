/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2020-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.eval;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
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
import java.time.LocalDateTime;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;
import org.apache.commons.lang3.time.StopWatch;

public final class RoundBasedStratumEvaluator extends AbstractStratumEvaluator {

  private final int stratumNum;
  private final SortedIndexedFactDb db;
  private SortedIndexedFactDb deltaDb;
  private SortedIndexedFactDb nextDeltaDb;
  private final Set<RelationSymbol> trackedRelations;
  private volatile boolean changed;

  private static final int taskSize = Configuration.taskSize;
  private static final int smtTaskSize = Configuration.smtTaskSize;

  public RoundBasedStratumEvaluator(
      int stratumNum,
      SortedIndexedFactDb db,
      SortedIndexedFactDb deltaDb,
      SortedIndexedFactDb nextDeltaDb,
      Iterable<IndexedRule> rules,
      CountingFJP exec,
      Set<RelationSymbol> trackedRelations) {
    super(rules, exec);
    this.stratumNum = stratumNum;
    this.db = db;
    this.deltaDb = deltaDb;
    this.nextDeltaDb = nextDeltaDb;
    this.trackedRelations = trackedRelations;
  }

  @Override
  public void evaluate() throws EvaluationException {
    this.deltaDb.clear();
    this.nextDeltaDb.clear();
    final boolean oneRuleAtATime = Configuration.oneRuleAtATime;
    int round = 0;
    StopWatch watch = recordRoundStart(round);
    for (IndexedRule r : firstRoundRules) {
      exec.externallyAddTask(new RulePrefixEvaluator(r));
      if (oneRuleAtATime) {
        exec.blockUntilFinishedExn();
      }
    }
    exec.blockUntilFinishedExn();
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
            if (oneRuleAtATime) {
              exec.blockUntilFinishedExn();
            }
          }
        }
      }
      exec.blockUntilFinishedExn();
      recordRoundEnd(round, watch);
      updateDbs();
    }
  }

  @Override
  protected final void reportFact(RelationSymbol sym, Term[] args) {
    var copy = args.clone();
    if (nextDeltaDb.add(sym, copy)) {
      changed = true;
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
  protected final boolean checkFact(RelationSymbol sym, Term[] args, Substitution s, Term[] scratch)
      throws EvaluationException {
    for (int i = 0; i < args.length; ++i) {
      scratch[i] = args[i].normalize(s);
    }
    return !db.hasFact(sym, scratch) && !nextDeltaDb.hasFact(sym, scratch);
  }

  private void updateDbs() {
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
  private class UpdateDbTask extends AbstractFJPTask {

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

  @Override
  protected final Iterable<Iterable<Term[]>> lookup(
      IndexedRule r, int pos, OverwriteSubstitution s, boolean split) throws EvaluationException {
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
    Iterable<Term[]> ans;
    if (sym instanceof DeltaSymbol) {
      ans = deltaDb.get(((DeltaSymbol) sym).getBaseSymbol(), key, idx);
    } else {
      ans = db.get(sym, key, idx);
    }
    if (split) {
      boolean smtSplit = splitPositions.get(r)[pos];
      int targetSize = smtSplit ? smtTaskSize : taskSize;
      return Util.splitIterable(ans, targetSize);
    } else if (ans.iterator().hasNext()) {
      return Collections.singletonList(ans);
    } else {
      return Collections.emptyList();
    }
  }

  @SuppressWarnings("serial")
  private class RulePrefixEvaluator extends AbstractFJPTask {

    private final IndexedRule rule;

    protected RulePrefixEvaluator(IndexedRule rule) {
      super(exec);
      this.rule = rule;
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
      Term[] scratch = new Term[head.getSymbol().getArity()];
      int checkPos = checkPosition.get(rule);
      loop:
      for (; pos <= len; ++pos) {
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
                if (lookup(rule, pos, s, false).iterator().hasNext()) {
                  return;
                }
              } else {
                // Stop on the first positive user predicate.
                break loop;
              }
              break;
          }
        } catch (EvaluationException e) {
          throw new EvaluationException(
              "Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
        }
      }
      Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s, true).iterator();
      if (tups.hasNext()) {
        new RuleSuffixEvaluator(rule, pos, s, tups, scratch.clone()).doTask();
      }
    }
  }

  private StopWatch recordRoundStart(int round) {
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

  private void recordRoundEnd(int round, StopWatch watch) {
    if (watch == null) {
      return;
    }
    watch.stop();
    System.err.println("[END] Stratum " + stratumNum + ", round " + round);
    System.err.println("Time: " + watch.getTime() + "ms");
  }

  private StopWatch recordDbUpdateStart() {
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

  private void recordDbUpdateEnd(StopWatch watch) {
    if (watch == null) {
      return;
    }
    watch.stop();
    Configuration.printRelSizes(System.err, "DELTA SIZE", deltaDb, false);
    System.err.println("[END] Updating DBs");
    System.err.println("Time: " + watch.getTime() + "ms");
  }
}
