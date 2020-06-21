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

import edu.harvard.seas.pl.formulog.eval.EvalUtil;
import edu.harvard.seas.pl.formulog.eval.IndexedRule;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.Stratum;

public class StratumCodeGen {

	private final CodeGenContext ctx;
	private static final CppVar changed = CppVar.mk("changed");

	public StratumCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public CppStmt gen(Stratum stratum) {
		List<CppStmt> stmts = new ArrayList<>();
		stmts.add(CppDecl.mk("changed", CppConst.mkFalse()));
		RuleCodeGen rcg = new RuleCodeGen(ctx);
		List<IndexedRule> noDeltaRules = new ArrayList<>();
		List<IndexedRule> deltaRules = new ArrayList<>();
		for (RelationSymbol sym : stratum.getPredicateSyms()) {
			for (IndexedRule r : ctx.getEval().getRules(sym)) {
				if (EvalUtil.findDelta(r) != null) {
					deltaRules.add(r);
				} else {
					noDeltaRules.add(r);
				}
			}
		}
		stmts.add(genFirstRound(stratum, noDeltaRules, rcg));
		stmts.add(genLoop(stratum, deltaRules, rcg));
		return CppSeq.mk(stmts);
	}

	private CppStmt genFirstRound(Stratum stratum, Iterable<IndexedRule> rules, RuleCodeGen rcg) {
		List<CppStmt> stmts = new ArrayList<>();
		stmts.add(genRules(rules, rcg, true));
		for (RelationSymbol sym : stratum.getPredicateSyms()) {
			Relation rel = ctx.lookupRelation(sym);
			Relation delta = ctx.lookupRelation(new DeltaSymbol(sym));
			stmts.add(delta.mkInsertAll(CppUnop.mkDeref(rel)).toStmt());
		}
		return CppSeq.mk(stmts);
	}

	private CppStmt genRules(Iterable<IndexedRule> rules, RuleCodeGen rcg, boolean isFirstRound) {
		List<CppStmt> stmts = new ArrayList<>();
		for (IndexedRule r : rules) {
			stmts.add(genRule(r, rcg, isFirstRound));
		}
		return CppSeq.mk(stmts);
	}

	private CppStmt genRule(IndexedRule r, RuleCodeGen rcg, boolean firstRound) {
		Pair<CppStmt, CppExpr> p = rcg.gen(r, firstRound);
		return CppSeq.mk(p.fst(), CppBinop.mkOrUpdate(changed, p.snd()).toStmt());
	}

	private CppStmt genLoop(Stratum stratum, Iterable<IndexedRule> rules, RuleCodeGen rcg) {
		CppStmt setFalse = CppBinop.mkAssign(changed, CppConst.mkFalse()).toStmt();
		CppStmt evalCode = genRules(rules, rcg, false);
		CppStmt updateCode = genUpdateCode(stratum);
		return CppWhile.mk(changed, CppSeq.mk(setFalse, evalCode, updateCode));
	}

	private CppStmt genUpdateCode(Stratum stratum) {
		List<CppStmt> stmts = new ArrayList<>();
		for (RelationSymbol sym : stratum.getPredicateSyms()) {
			Relation rel = ctx.lookupRelation(sym);
			Relation delta = ctx.lookupRelation(new DeltaSymbol(sym));
			Relation newRel = ctx.lookupRelation(new NewSymbol(sym));
			stmts.add(rel.mkInsertAll(CppUnop.mkDeref(newRel)).toStmt());
			stmts.add(delta.mkPurge());
			stmts.add(CppFuncCall.mk("swap", delta, newRel).toStmt());
		}
		return CppSeq.mk(stmts);
	}

}
