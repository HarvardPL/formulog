package edu.harvard.seas.pl.formulog.codegen;

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

import java.util.ArrayList;
import java.util.List;

import edu.harvard.seas.pl.formulog.eval.IndexedRule;
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
		stmts.add(genFirstRound(stratum, rcg));
		stmts.add(genLoop(stratum, rcg));
		return CppSeq.mk(stmts);
	}

	private CppStmt genFirstRound(Stratum stratum, RuleCodeGen rcg) {
		List<CppStmt> stmts = new ArrayList<>();
		for (RelationSymbol sym : stratum.getPredicateSyms()) {
			stmts.add(genFirstRound(sym, rcg));
		}
		return CppSeq.mk(stmts); 
	}
	
	private CppStmt genFirstRound(RelationSymbol sym, RuleCodeGen rcg) {
		List<CppStmt> stmts = new ArrayList<>();
		for (IndexedRule r : ctx.getEval().getFirstRoundRules(sym)) {
			stmts.add(genRule(r, rcg, true));
		}
		return CppSeq.mk(stmts);
	}
	
	private CppStmt genRule(IndexedRule r, RuleCodeGen rcg, boolean firstRound) {
		Pair<CppStmt, CppExpr> p = rcg.gen(r, firstRound);
		return CppSeq.mk(p.fst(), CppBinop.mkOrUpdate(changed, p.snd()).toStmt());
	}
	
	private CppStmt genLoop(Stratum stratum, RuleCodeGen rcg) {
		CppStmt setFalse = CppBinop.mkAssign(changed, CppConst.mkFalse()).toStmt();
		return CppWhile.mk(changed, CppSeq.mk(setFalse, genLaterRounds(stratum, rcg)));
	}
	
	private CppStmt genLaterRounds(Stratum stratum, RuleCodeGen rcg) {
		return CppSeq.skip();
	}

}
