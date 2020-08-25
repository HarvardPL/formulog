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

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.db.IndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.magic.AdornedSymbol;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.OverwriteSubstitution;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.*;
import org.apache.commons.lang3.time.StopWatch;

import java.time.LocalDateTime;
import java.util.*;

public final class BalbinEvaluationContext extends AbstractStratumEvaluator {

    Iterable<IndexedRule> rules;
    Map<RelationSymbol, Set<IndexedRule>> allRules;
    final SortedIndexedFactDb db;
    IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb;
    SortedIndexedFactDb deltaDb;
    SortedIndexedFactDb nextDeltaDb;
    RelationSymbol qSymbol;
    Set<Term[]> qMagicFactsTerms;
    final CountingFJP exec;
    final Set<RelationSymbol> trackedRelations;
    volatile boolean changed;
    MagicSetTransformer mst;
    int maxPathLength;

    static final int taskSize = Configuration.taskSize;
    static final int smtTaskSize = Configuration.smtTaskSize;

    public BalbinEvaluationContext(SortedIndexedFactDb db, IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb,
                                   RelationSymbol qSymbol, Set<Term[]> qMagicFactsTerms, Iterable<IndexedRule> rules,
                                   Map<RelationSymbol, Set<IndexedRule>> allRules, CountingFJP exec,
                                   Set<RelationSymbol> trackedRelations, MagicSetTransformer mst, int maxPathLength) {
        super(rules);
        this.rules = rules;
        this.allRules = allRules;
        this.db = db;
        this.deltaDbb = deltaDbb;
        this.deltaDb = deltaDbb.build();
        this.nextDeltaDb = deltaDbb.build();
        this.qSymbol = qSymbol;
        this.qMagicFactsTerms = qMagicFactsTerms;
        this.exec = exec;
        this.trackedRelations = trackedRelations;
        this.mst = mst;
        this.maxPathLength = maxPathLength;

        System.out.println("HELLO");
        assert qSymbol instanceof MagicSetTransformer.InputSymbol : "Balbin evaluation context: Query must be an InputSymbol";
        addQMagicFactsToDb(db);
        addQMagicFactsToDb(deltaDb);
    }

    private void addQMagicFactsToDb(SortedIndexedFactDb db) {
        exec.externallyAddTask(new AbstractFJPTask(exec) {

            @Override
            public void doTask() throws EvaluationException {
                for (Term[] tup : qMagicFactsTerms) {
                    try {
                        db.add(qSymbol, Terms.normalize(tup, new SimpleSubstitution()));
                    } catch (EvaluationException e) {
                        UserPredicate p = UserPredicate.make(qSymbol, tup, false);
                        throw new EvaluationException("Cannot normalize fact " + p + ":\n" + e.getMessage());
                    }
                }
            }

        });
    }

    @Override
    public void evaluate() throws EvaluationException {
        int round = 0;
        StopWatch watch = recordRoundStart(round);

        for (IndexedRule r : rules) {
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
            for (RelationSymbol delta : deltaRules.keySet()) {
                if (!deltaDb.isEmpty(delta)) {
                    for (IndexedRule r : deltaRules.get(delta)) {
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
        Iterable<Term[]> ans;
        if (sym instanceof SemiNaiveRule.DeltaSymbol) {
            ans = deltaDb.get(((SemiNaiveRule.DeltaSymbol) sym).getBaseSymbol(), key, idx);
        } else {
            ans = db.get(sym, key, idx);
        }
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
                                SimplePredicate lPred = (SimplePredicate) l;
                                if (lPred.isNegated()) {
                                    // Check whether there exists a SIPS arc to lPred
                                    if (mst.exploreTopDown(lPred.getSymbol())) {
                                        // Apply substitution, which returns a new UserPredicate
                                        UserPredicate newLPred = applySubstitutionToNegLiteralWithNegArc(lPred.getSymbol(), lPred.getArgs(), s);
                                        // Create input atom
                                        UserPredicate newLInputAtom = MagicSetTransformer.createInputAtom(newLPred);
                                        RelationSymbol newLInputSymbol = newLInputAtom.getSymbol();
                                        // Get prules
                                        List<IndexedRule> pRules = new ArrayList<>();
                                        pRules.addAll(BalbinEvaluation.getPRules(newLInputAtom, allRules, maxPathLength));
                                        System.out.println("newLInputAtom: " + newLInputAtom);
                                        System.out.println("pRules: " + pRules);

                                        // Evaluate a new context
                                        Set<Term[]> newQMagicFactsTerms = new HashSet<>();
                                        newQMagicFactsTerms.add(newLInputAtom.getArgs());
                                        new BalbinEvaluationContext(db, deltaDbb, newLInputAtom.getSymbol(), newQMagicFactsTerms, pRules, allRules,
                                                exec, trackedRelations, mst, maxPathLength).evaluate();
                                    } else {
                                        if (!tups.hasNext()) {
                                            pos++;
                                        } else {
                                            pos--;
                                            movingRight = false;
                                        }
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

        protected RulePrefixEvaluator(IndexedRule rule) {
            super(exec);
            this.rule = rule;
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
                            SimplePredicate lPred = (SimplePredicate) l;
                            if (lPred.isNegated()) {
                                // Check whether there exists a SIPS arc to lPred
                                if (mst.exploreTopDown(lPred.getSymbol())) {
                                    // Apply substitution, which returns a new UserPredicate
                                    UserPredicate newLPred = applySubstitutionToNegLiteralWithNegArc(lPred.getSymbol(), lPred.getArgs(), s);
                                    // Create input atom
                                    UserPredicate newLInputAtom = MagicSetTransformer.createInputAtom(newLPred);
                                    RelationSymbol newLInputSymbol = newLInputAtom.getSymbol();
                                    // Get prules
                                    List<IndexedRule> pRules = new ArrayList<>();
                                    pRules.addAll(BalbinEvaluation.getPRules(newLInputAtom, allRules, maxPathLength));

                                    // Evaluate a new context
                                    Set<Term[]> newQMagicFactsTerms = new HashSet<>();
                                    newQMagicFactsTerms.add(newLInputAtom.getArgs());
                                    new BalbinEvaluationContext(db, deltaDbb, newLInputAtom.getSymbol(), newQMagicFactsTerms, pRules, allRules,
                                            exec, trackedRelations, mst, maxPathLength).evaluate();
                                } else {
                                    if (lookup(rule, pos, s).iterator().hasNext()) {
                                        return;
                                    }
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
            if (pos == len) {
                try {
                    SimplePredicate head = rule.getHead();
                    reportFact(head.getSymbol(), head.getArgs(), s);
                    return;
                } catch (EvaluationException e) {
                    throw new EvaluationException("Exception raised while evaluationg the literal: " + rule.getHead()
                            + e.getLocalizedMessage());
                }
            }
            Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s).iterator();
            if (tups.hasNext()) {
                exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, pos, s, tups));
            }
        }
    }

    UserPredicate applySubstitutionToNegLiteralWithNegArc(RelationSymbol sym, Term[] args, Substitution s) throws EvaluationException {
        Term[] newArgs = new Term[args.length];
        for (int i = 0; i < args.length; ++i) {
            newArgs[i] = args[i].normalize(s);
        }
        return UserPredicate.make(sym, newArgs, true);
    }

    StopWatch recordRoundStart(int round) {
        if (!Configuration.debugRounds) {
            return null;
        }
        System.err.println("#####");
        System.err.println("[START] Round " + round);
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
        System.err.println("[END] Round " + round);
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

