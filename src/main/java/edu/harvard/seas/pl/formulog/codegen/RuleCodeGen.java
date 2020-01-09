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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.IndexedRule;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.TodoException;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralTag;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public class RuleCodeGen {

	private final CodeGenContext ctx;
	private final TermCodeGen tcg;

	public RuleCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
		this.tcg = new TermCodeGen(ctx);
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
		private boolean hasReachedSplit;
		private boolean hasCheckedForNovelty;
		private final Map<Var, CppExpr> env = new HashMap<>();

		public Worker(IndexedRule rule, boolean isFirstRound) {
			this.rule = rule;
			this.isFirstRound = isFirstRound;
		}

		private Function<CppStmt, CppStmt> makeEvalCode() {
			Function<CppStmt, CppStmt> continuation = x -> x;
			int pos = 0;
			Set<Var> boundVars = new HashSet<>();
			for (SimpleLiteral l : rule) {
				Function<CppStmt, CppStmt> k; 
				if (!hasCheckedForNovelty && boundVars.containsAll(rule.getHead().varSet())) {
					final Function<CppStmt, CppStmt> k2 = l.accept(visitor, pos);
					k = s -> mkCheckIfNew().apply(k2.apply(s));
					hasCheckedForNovelty = true;
				} else {
					k = l.accept(visitor, pos);
				}
				final Function<CppStmt, CppStmt> k2 = continuation;
				continuation = s -> k2.apply(k.apply(s));
				boundVars.addAll(l.varSet());
				pos++;
			}
			return continuation;
		}
		
		public Pair<CppStmt, CppExpr> go() {
			Function<CppStmt, CppStmt> evalCode = makeEvalCode();
			Pair<CppStmt, CppExpr> update = mkDbUpdate();
			return new Pair<>(evalCode.apply(update.fst()), update.snd());
		}
		
		private Pair<CppStmt, CppExpr> mkDbUpdate() {
			Relation rel = getTargetRel();
			CppStmt stmt = rel.mkInsert(CppVar.mk("tuple")).toStmt();
			if (!hasCheckedForNovelty && !isFirstRound) {
				stmt = mkCheckIfNew().apply(stmt);
			} else if (!hasCheckedForNovelty) {
				stmt = CppSeq.mk(declTuple(), stmt);
			}
			return new Pair<>(stmt, CppUnop.mkNot(rel.mkIsEmpty()));
		}
		
		private Function<CppStmt, CppStmt> mkCheckIfNew() {
			Relation rel = ctx.lookupRelation(rule.getHead().getSymbol());
			CppExpr guard = CppUnop.mkNot(rel.mkContains(CppVar.mk("tuple")));
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

		private final SimpleLiteralVisitor<Integer, Function<CppStmt, CppStmt>> visitor = new SimpleLiteralVisitor<Integer, Function<CppStmt, CppStmt>>() {

			@Override
			public Function<CppStmt, CppStmt> visit(Assignment assignment, Integer pos) {
				return handleAssignment(assignment);
			}

			@Override
			public Function<CppStmt, CppStmt> visit(Check check, Integer pos) {
				return handleCheck(check);
			}

			@Override
			public Function<CppStmt, CppStmt> visit(Destructor destructor, Integer pos) {
				return handleDestructor(destructor);
			}

			@Override
			public Function<CppStmt, CppStmt> visit(SimplePredicate pred, Integer pos) {
				if (pred.isNegated()) {
					return handleNegativePred(pred, pos);
				} else {
					return handlePositivePred(pred, pos);
				}
			}

		};

		private Function<CppStmt, CppStmt> handleAssignment(Assignment assignment) {
			throw new TodoException();
		}

		private Function<CppStmt, CppStmt> handleCheck(Check check) {
			throw new TodoException();
		}

		private Function<CppStmt, CppStmt> handleDestructor(Destructor destructor) {
			throw new TodoException();
		}

		private Function<CppStmt, CppStmt> handleNegativePred(SimplePredicate pred, int pos) {
			throw new TodoException();
		}

		private Function<CppStmt, CppStmt> handlePositivePred(SimplePredicate pred, int pos) {
			Pair<Function<CppStmt, CppStmt>, CppExpr> p = genTupleIterator(pred, pos);
			Function<CppStmt, CppStmt> loop = genLoop(pred, pos, p.snd());
			return s -> p.fst().apply(loop.apply(s));
		}

		private Pair<Function<CppStmt, CppStmt>, CppExpr> genTupleIterator(SimplePredicate pred, int pos) {
			if (!hasReachedSplit) {
				hasReachedSplit = true;
				return genParallelLoop(pred);
			} else {
				return genNormalLookup(pred, pos);
			}
		}

		private Pair<Function<CppStmt, CppStmt>, CppExpr> genParallelLoop(SimplePredicate pred) {
			BindingType[] pat = pred.getBindingPattern();
			for (BindingType binding : pat) {
				if (binding != BindingType.FREE) {
					throw new TodoException();
				}
			}
			CppStmt assign = CppDecl.mk("part", lookupRelation(pred).mkPartition());
			CppVar it = CppVar.mk("it");
			CppExpr init = CppMethodCall.mk(CppVar.mk("part"), "begin");
			CppExpr guard = CppBinop.mkLt(it, CppMethodCall.mk(CppVar.mk("part"), "end"));
			CppExpr update = CppUnop.mkPreIncr(it);
			Function<CppStmt, CppStmt> forLoop = body -> CppFor.mk("it", init, guard, update, body);
			return new Pair<>(body -> CppSeq.mk(assign, forLoop.apply(body)), CppUnop.mkDeref(it));
		}
		
		private Pair<Function<CppStmt, CppStmt>, CppExpr> genNormalLookup(SimplePredicate pred, int pos) {
			List<CppStmt> stmts = new ArrayList<>();
			String tupName = ctx.newId("key");
			CppVar tup = CppVar.mk(tupName);
			Relation rel = ctx.lookupRelation(pred.getSymbol());
			stmts.add(rel.mkDeclTuple(tupName));
			Term[] args = pred.getArgs();
			int i = 0;
			for (BindingType ty : pred.getBindingPattern()) {
				if (ty == BindingType.BOUND) {
					Pair<CppStmt, CppExpr> p = tcg.gen(args[i], env);
					stmts.add(p.fst());
					CppExpr idx = CppConst.mkInt(i);
					stmts.add(CppBinop.mkAssign(CppSubscript.mk(tup, idx), p.snd()).toStmt());
				}
				i++;
			}
			CppExpr call = rel.mkLookup(rule.getDbIndex(pos), Arrays.asList(pred.getBindingPattern()), tup);
			CppStmt all = CppSeq.mk(stmts);
			return new Pair<>(s -> CppSeq.mk(all, s), call);
		}

		private Function<CppStmt, CppStmt> genLoop(SimplePredicate pred, int pos, CppExpr it) {
			Relation rel = lookupRelation(pred);
			String tup = ctx.newId("tup");
			List<CppStmt> assignments = new ArrayList<>();
			BindingType[] pat = pred.getBindingPattern();
			int i = 0;
			for (Term t : pred.getArgs()) {
				if (pat[i] == BindingType.FREE) {
					String id = ctx.newId("x");
					CppExpr access = rel.mkTupleAccess(CppVar.mk(tup), CppConst.mkInt(i));
					assignments.add(CppDecl.mkRef(id, access));
					env.put((Var) t, CppVar.mk(id));
				}
				i++;
			}
			CppStmt all = CppSeq.mk(assignments);
			return s -> CppForEach.mk(tup, it, CppSeq.mk(all, s));
		}

		private Relation lookupRelation(SimplePredicate pred) {
			return ctx.lookupRelation(pred.getSymbol());
		}

	}

}
