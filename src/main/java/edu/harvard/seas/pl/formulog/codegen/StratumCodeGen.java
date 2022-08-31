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

import java.util.ArrayList;
import java.util.List;

import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.eval.EvalUtil;
import edu.harvard.seas.pl.formulog.eval.IndexedRule;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.Stratum;

/**
 * This class is used to take a stratum (from a stratified Formulog program) and
 * generate C++ code that evaluates it. This class implements semi-naive
 * evaluation.
 */
public class StratumCodeGen {

//    private final CodeGenContext ctx;
//    /**
//     * This variable is used in the C++ code to track whether a new tuple has been
//     * derived; if so, we need to keep evaluating, since we've yet to reach a fix
//     * point.
//     */
//    private static final CppVar changed = CppVar.mk("changed");
//
//    public StratumCodeGen(CodeGenContext ctx) {
//        this.ctx = ctx;
//    }
//
//    /**
//     * Take a stratum (from a stratified Formulog program) and generate C++ code
//     * that evaluates it.
//     *
//     * @param stratum
//     * @return The C++ representation of the stratum evaluation
//     */
//    public CppStmt gen(Stratum stratum) {
//        List<CppStmt> stmts = new ArrayList<>();
//        stmts.add(CppDecl.mk("changed", CppConst.mkFalse()));
//        RuleCodeGen rcg = new RuleCodeGen(ctx);
//        // Split rules into first-round rules (which refer to predicates from only lower
//        // strata, and so only need to be executed once) and later-round rules, which
//        // need to be executed in a loop until a fix point is reached.
//        List<IndexedRule> firstRoundRules = new ArrayList<>();
//        List<IndexedRule> laterRoundRules = new ArrayList<>();
//        for (RelationSymbol sym : stratum.getPredicateSyms()) {
//            for (IndexedRule r : ctx.getEval().getRules(sym)) {
//                if (EvalUtil.findDelta(r) != null) {
//                    laterRoundRules.add(r);
//                } else {
//                    firstRoundRules.add(r);
//                }
//            }
//        }
//        stmts.add(genFirstRound(stratum, firstRoundRules, rcg));
//        stmts.add(genLoop(stratum, laterRoundRules, rcg));
//        return CppSeq.mk(stmts);
//    }
//
//    /**
//     * Generate C++ code for evaluating the first-round rules. These are rules that
//     * refer to predicates from only lower strata, and so only need to be evaluated
//     * once.
//     *
//     * @param stratum
//     * @param rules
//     * @param rcg
//     * @return The C++ code for evaluating the first-round rules
//     */
//    private CppStmt genFirstRound(Stratum stratum, Iterable<IndexedRule> rules, RuleCodeGen rcg) {
//        List<CppStmt> stmts = new ArrayList<>();
//        stmts.add(genRules(rules, rcg, true));
//        for (RelationSymbol sym : stratum.getPredicateSyms()) {
//            Relation rel = ctx.lookupRelation(sym);
//            Relation delta = ctx.lookupRelation(new DeltaSymbol(sym));
//            // Insert anything we've derived into the Delta DB
//            stmts.add(delta.mkInsertAll(CppUnop.mkDeref(rel)).toStmt());
//        }
//        return CppSeq.mk(stmts);
//    }
//
//    /**
//     * Take a bunch of rules and generate code for running each of those rules once.
//     *
//     * @param rules
//     * @param rcg
//     * @param isFirstRound
//     * @return The C++ code for running the rules
//     */
//    private CppStmt genRules(Iterable<IndexedRule> rules, RuleCodeGen rcg, boolean isFirstRound) {
//        List<CppStmt> stmts = new ArrayList<>();
//        for (IndexedRule r : rules) {
//            stmts.add(genRule(r, rcg, isFirstRound));
//        }
//        return CppSeq.mk(stmts);
//    }
//
//    /**
//     * Take a rule and generate code for running that rule once.
//     *
//     * @param r
//     * @param rcg
//     * @param firstRound
//     * @return The C++ code for running the rule
//     */
//    private CppStmt genRule(IndexedRule r, RuleCodeGen rcg, boolean firstRound) {
//        Pair<CppStmt, CppExpr> p = rcg.gen(r, firstRound);
//        // Make sure the changed variable is updated to true if the rule derived
//        // something new
//        return CppSeq.mk(p.fst(), CppBinop.mkOrUpdate(changed, p.snd()).toStmt());
//    }
//
//    /**
//     * Generate a loop for running the later-round rules until a fix point is
//     * reached.
//     *
//     * @param stratum
//     * @param rules
//     * @param rcg
//     * @return The C++ code for the loop
//     */
//    private CppStmt genLoop(Stratum stratum, Iterable<IndexedRule> rules, RuleCodeGen rcg) {
//        CppStmt setFalse = CppBinop.mkAssign(changed, CppConst.mkFalse()).toStmt();
//        CppStmt evalCode = genRules(rules, rcg, false);
//        CppStmt updateCode = genUpdateCode(stratum);
//        return CppWhile.mk(changed, CppSeq.mk(setFalse, evalCode, updateCode));
//    }
//
//    /**
//     * Generate C++ code for updating the fact databases after an iteration of the
//     * evaluation loop.
//     *
//     * @param stratum
//     * @return The C++ code for updating the databases
//     */
//    private CppStmt genUpdateCode(Stratum stratum) {
//        List<CppStmt> stmts = new ArrayList<>();
//        for (RelationSymbol sym : stratum.getPredicateSyms()) {
//            // The generated C++ code for rule evaluation puts newly derived stuff in
//            // newRel, so here we add that stuff to the cumulative DB for that relation and
//            // set the Delta DB to be newRel (so that the new tuples are used as the "delta"
//            // tuples in the next iteration of evaluation).
//            Relation rel = ctx.lookupRelation(sym);
//            Relation delta = ctx.lookupRelation(new DeltaSymbol(sym));
//            Relation newRel = ctx.lookupRelation(new NewSymbol(sym));
//            stmts.add(rel.mkInsertAll(CppUnop.mkDeref(newRel)).toStmt());
//            stmts.add(delta.mkPurge());
//            stmts.add(CppFuncCall.mk("swap", delta, newRel).toStmt());
//        }
//        return CppSeq.mk(stmts);
//    }

}
