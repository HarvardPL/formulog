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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.LiteralCodeGen.Result;
import edu.harvard.seas.pl.formulog.codegen.LiteralCodeGen.ResultType;
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

public class RuleCodeGen {

	private final CodeGenContext ctx;

	public RuleCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public Pair<CppStmt, CppExpr> gen(IndexedRule rule, boolean isFirstRound) {
		Function<CppStmt, CppStmt> outerIf = mkOuterIf(rule);
		Pair<CppStmt, CppExpr> evalCode = new Worker(rule, isFirstRound).go();
		CppStmt code = outerIf.apply(evalCode.fst());
		return new Pair<>(code, evalCode.snd());
	}

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
		private final boolean isFirstRound;
		private final LiteralCodeGen lcg = new LiteralCodeGen(ctx);
		private final TermCodeGen tcg = new TermCodeGen(ctx);
		private boolean hasReachedSplit;
		private boolean hasCheckedForNovelty;
		private Map<Var, CppExpr> env = new HashMap<>();

		public Worker(IndexedRule rule, boolean isFirstRound) {
			this.rule = rule;
			this.isFirstRound = isFirstRound;
		}
		
		private Set<Relation> makeHints(int pos) {
			Set<Relation> s = new HashSet<>();
			s.add(getTargetRel());
			if (!hasCheckedForNovelty) {
				s.add(ctx.lookupRelation(rule.getHead().getSymbol()));
			}
			int stop = hasReachedSplit ? pos : pos + 1;
			for (int i = rule.getBodySize() - 1; i >= stop; --i) {
				SimpleLiteral l = rule.getBody(i);
				if (l instanceof SimplePredicate) {
					RelationSymbol sym = ((SimplePredicate) l).getSymbol();
					s.add(ctx.lookupRelation(sym));
				}
			}
			return s;
		}

		private Function<CppStmt, CppStmt> makeEvalCode() {
			Function<CppStmt, CppStmt> continuation = x -> x;
			int pos = 0;
			Set<Var> boundVars = new HashSet<>();
			for (SimpleLiteral l : rule) {
				Function<CppStmt, CppStmt> k;
				lcg.setHints(makeHints(pos));
				if (hasReachedSplit) {
					lcg.enableHints();
				}
				Result res = l.accept(visitor, pos);
				if (!hasCheckedForNovelty && boundVars.containsAll(rule.getHead().varSet())) {
					boolean b = hasReachedSplit;
					k = s -> mkCheckIfNew(b).apply(res.getK().apply(s));
					hasCheckedForNovelty = true;
				} else {
					k = res.getK();
				}
				hasReachedSplit |= res.getResType() == ResultType.PARALLEL_LOOP;
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
				return lcg.gen(predicate, rule.getDbIndex(pos), !hasReachedSplit, env);
			}
			
		};

		public Pair<CppStmt, CppExpr> go() {
			Function<CppStmt, CppStmt> evalCode = makeEvalCode();
			Pair<CppStmt, CppExpr> update = mkDbUpdate();
			return new Pair<>(evalCode.apply(update.fst()), update.snd());
		}

		private Pair<CppStmt, CppExpr> mkDbUpdate() {
			Relation rel = getTargetRel();
			CppStmt stmt = rel.mkInsert(CppVar.mk("tuple"), hasReachedSplit).toStmt();
			if (!hasCheckedForNovelty && !isFirstRound) {
				stmt = mkCheckIfNew(hasReachedSplit).apply(stmt);
			} else if (!hasCheckedForNovelty) {
				stmt = CppSeq.mk(declTuple(), stmt);
			}
			return new Pair<>(stmt, CppUnop.mkNot(rel.mkIsEmpty()));
		}

		private Function<CppStmt, CppStmt> mkCheckIfNew(boolean hasReachedSplit) {
			Relation rel = ctx.lookupRelation(rule.getHead().getSymbol());
			CppExpr guard = CppUnop.mkNot(rel.mkContains(CppVar.mk("tuple"), hasReachedSplit));
			return s -> CppSeq.mk(declTuple(), CppIf.mk(guard, s));
		}

		private CppStmt declTuple() {
			Relation rel = getTargetRel();
			Pair<CppStmt, List<CppExpr>> p = tcg.gen(Arrays.asList(rule.getHead().getArgs()), env);
			CppStmt declTuple = rel.mkDeclTuple("tuple", p.snd());
			return CppSeq.mk(p.fst(), declTuple);
		}

		private Relation getTargetRel() {
			SimplePredicate head = rule.getHead();
			RelationSymbol sym = isFirstRound ? head.getSymbol() : new NewSymbol(head.getSymbol());
			return ctx.lookupRelation(sym);
		}

	}

}
