package edu.harvard.seas.pl.formulog.codegen;

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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.LiteralCodeGen.Result;
import edu.harvard.seas.pl.formulog.codegen.LiteralCodeGen.CodeShape;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.eval.IndexedRule;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralTag;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

/**
 * This class takes a Formulog rule and generates C++ code for evaluating that
 * rule.
 */
public class RuleCodeGen {

    private final CodeGenContext ctx;

    public RuleCodeGen(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    /**
     * Take a Formulog rule and generate C++ code for evaluating it. The nature of
     * the generated code depends on whether the rule is a "first-round rule" (does
     * not depend on predicates defined in the same stratum) or a "later-round rule"
     * (depends on predicates defined in the same stratum).
     *
     * @param rule
     * @param isFirstRound
     * @return A pair of a C++ statement and a C++ expression. The statement is the
     * code for running the rule; the expression is a boolean value
     * indicating whether running the rule has resulted in new tuples being
     * derived.
     */
    public Pair<CppStmt, CppExpr> gen(IndexedRule rule, boolean isFirstRound) {
        Function<CppStmt, CppStmt> outerIf = mkOuterIf(rule);
        Pair<CppStmt, CppExpr> evalCode = new Worker(rule, isFirstRound).go();
        CppStmt code = outerIf.apply(evalCode.fst());
        return new Pair<>(code, evalCode.snd());
    }

    /**
     * Stick an if around the evaluation of a rule that makes sure no relation
     * referred to positively in the body of the rule is empty (if this condition is
     * not met, the rule will cannot succeed, so there's no point in running it).
     *
     * @param rule
     * @return A continuation that expects the code for running the rule
     */
    private Function<CppStmt, CppStmt> mkOuterIf(IndexedRule rule) {
        Set<RelationSymbol> syms = new HashSet<>();
        for (SimpleLiteral l : rule) {
            if (l.getTag() == SimpleLiteralTag.PREDICATE) {
                SimplePredicate pred = (SimplePredicate) l;
                if (!pred.isNegated()) {
                    syms.add(pred.getSymbol());
                }
            }
        }
        CppExpr guard = CppConst.mkTrue();
        for (RelationSymbol sym : syms) {
            Relation rel = ctx.lookupRelation(sym);
            CppExpr notEmpty = CppUnop.mkNot(rel.mkIsEmpty());
            guard = CppBinop.mkLogAnd(guard, notEmpty);
        }
        final CppExpr guard2 = guard;
        return body -> CppIf.mk(guard2, body);
    }

    private class Worker {

        private final IndexedRule rule;
        /**
         * Does the rule refer to predicates from only lower strata?
         */
        private final boolean isFirstRound;
        private final LiteralCodeGen lcg = new LiteralCodeGen(ctx);
        private final TermCodeGen tcg = new TermCodeGen(ctx);
        /**
         * Have we reached the point in the rule where evaluation has been parallelized?
         * Hints are only created/used after we've started parallel evaluation.
         */
        private boolean doingParallelEval;
        /**
         * Have we checked whether the tuple we would derive is actually novel? (If it's
         * not, no reason to run the rest of the rule.)
         */
        private boolean hasCheckedForNovelty;
        private Map<Var, CppExpr> env = new HashMap<>();

        public Worker(IndexedRule rule, boolean isFirstRound) {
            this.rule = rule;
            this.isFirstRound = isFirstRound;
        }

        /**
         * Figure out for which relations we should use B-tree hints when we query them
         * during rule evaluation.
         *
         * @param pos Our current position in the rule body
         * @return The set of relations we want to use hints for
         */
        private Set<Relation> makeHints(int pos) {
            Set<Relation> s = new HashSet<>();
            // We can always use a hint for the relation that we'll be inserting a new tuple
            // into.
            s.add(getTargetRel());
            // If we haven't yet checked whether a tuple is novel, we can use a hint for
            // indexing into that tuples relation (when we check for novelty).
            if (!hasCheckedForNovelty) {
                s.add(ctx.lookupRelation(rule.getHead().getSymbol()));
            }
            // We can use a hint for any relation that is going to be queried during
            // parallel evaluation; if we're already doing parallel evaluation, then we need
            // to check any literal following *and including* the current one; if we are
            // not, then we need to check just the literals following the current one.
            int stop = doingParallelEval ? pos : pos + 1;
            for (int i = rule.getBodySize() - 1; i >= stop; --i) {
                SimpleLiteral l = rule.getBody(i);
                if (l instanceof SimplePredicate) {
                    RelationSymbol sym = ((SimplePredicate) l).getSymbol();
                    s.add(ctx.lookupRelation(sym));
                }
            }
            return s;
        }

        /**
         * Generate the C++ code for actually evaluating the rule (but not updating any
         * fact database)
         *
         * @return A continuation that expects any code we want to run after deriving a
         * novel tuple (such as code for update the fact databases)
         */
        private Function<CppStmt, CppStmt> makeEvalCode() {
            Function<CppStmt, CppStmt> continuation = x -> x;
            int pos = 0;
            Set<Var> boundVars = new HashSet<>();
            // Loop through the literals in the rule body, generating code one by one and
            // building up a big continuation
            for (SimpleLiteral l : rule) {
                Function<CppStmt, CppStmt> k;
                // Tell the literal code generator which B-tree hints we're using, and
                // whether to use them (we only should after evaluation has been parallelized).
                lcg.setHints(makeHints(pos));
                if (doingParallelEval) {
                    lcg.enableHints();
                }
                Result res = l.accept(visitor, pos);
                if (!hasCheckedForNovelty && boundVars.containsAll(rule.getHead().varSet())) {
                    // If all the variables in the rule head are bound, we can check to see if the
                    // tuple we are deriving is actually novel (and stop this thread of evaluation
                    // if not).
                    boolean b = doingParallelEval;
                    k = s -> mkCheckIfNew(b).apply(res.getK().apply(s));
                    hasCheckedForNovelty = true;
                } else {
                    k = res.getK();
                }
                // The literal code gen tells us whether it has generated a parallelized loop
                doingParallelEval |= res.getCodeShape() == CodeShape.PARALLEL_LOOP;
                env = res.getNewEnv();
                final Function<CppStmt, CppStmt> k2 = continuation;
                continuation = s -> k2.apply(k.apply(s));
                boundVars.addAll(l.varSet());
                pos++;
            }
            return continuation;
        }

        private SimpleLiteralVisitor<Integer, Result> visitor = new SimpleLiteralVisitor<Integer, Result>() {

            @Override
            public Result visit(Assignment assignment, Integer pos) {
                return lcg.gen(assignment, env);
            }

            @Override
            public Result visit(Check check, Integer pos) {
                return lcg.gen(check, env);
            }

            @Override
            public Result visit(Destructor destructor, Integer pos) {
                return lcg.gen(destructor, env);
            }

            @Override
            public Result visit(SimplePredicate predicate, Integer pos) {
                return lcg.gen(predicate, rule.getDbIndex(pos), !doingParallelEval, env);
            }

        };

        /**
         * Generate C++ code for the rule
         *
         * @return The C++ statement for evaluating the rule, plus a C++ expression that
         * evaluates to true if the rule has resulted in the derivation of a
         * novel tuple
         */
        public Pair<CppStmt, CppExpr> go() {
            Function<CppStmt, CppStmt> evalCode = makeEvalCode();
            CppStmt update = mkDbUpdate();
            CppExpr isNovel = CppUnop.mkNot(getTargetRel().mkIsEmpty());
            return new Pair<>(evalCode.apply(update), isNovel);
        }

        /**
         * Generate C++ code inserting the newly derived tuple into the right relation.
         *
         * @return The C++ statement for doing the insertion
         */
        private CppStmt mkDbUpdate() {
            Relation rel = getTargetRel();
            CppStmt stmt = rel.mkInsert(CppVar.mk("tuple"), doingParallelEval).toStmt();
            if (!hasCheckedForNovelty && !isFirstRound) {
                stmt = mkCheckIfNew(doingParallelEval).apply(stmt);
            } else if (!hasCheckedForNovelty) {
                stmt = CppSeq.mk(declTuple(), stmt);
            }
            return stmt;
        }

        /**
         * Generate a C++ conditional that checks whether the tuple that we are trying
         * to derive is actually novel (and thus we should continue the rule evaluation)
         * or not.
         *
         * @param doingParallelEval It takes this as an argument instead of using the member field
         *                          because we want to capture this value when this function is
         *                          called, not when the continuation it returns is invoked
         * @return A continuation that expects the code for evaluating the rest of the
         * rule
         */
        private Function<CppStmt, CppStmt> mkCheckIfNew(boolean doingParallelEval) {
            Relation rel = ctx.lookupRelation(rule.getHead().getSymbol());
            CppExpr guard = CppUnop.mkNot(rel.mkContains(CppVar.mk("tuple"), doingParallelEval));
            return s -> CppSeq.mk(declTuple(), CppIf.mk(guard, s));
        }

        /**
         * Generate a C++ statement that declares a variable "tuple" that represents the
         * current tuple that is being derived, and fills it up with the appropriate
         * arguments.
         *
         * @return The C++ declaration
         */
        private CppStmt declTuple() {
            Relation rel = getTargetRel();
            Pair<CppStmt, List<CppExpr>> p = tcg.gen(Arrays.asList(rule.getHead().getArgs()), env);
            CppStmt declTuple = rel.mkDeclTuple("tuple", p.snd());
            return CppSeq.mk(p.fst(), declTuple);
        }

        /**
         * Returns the relation that we're adding new tuples to; depends on whether it
         * is first-round rule or not.
         *
         * @return The relation we should add new tuples to
         */
        private Relation getTargetRel() {
            SimplePredicate head = rule.getHead();
            RelationSymbol sym = isFirstRound ? head.getSymbol() : new NewSymbol(head.getSymbol());
            return ctx.lookupRelation(sym);
        }

    }

}
