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
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Triple;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public class LiteralCodeGen {

	private final CodeGenContext ctx;

	public LiteralCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	private final Set<Relation> hints = new HashSet<>();
	private boolean hintsEnabled;

	public void setHints(Set<Relation> hints) {
		this.hints.clear();
		this.hints.addAll(hints);
	}

	public void enableHints() {
		hintsEnabled = true;
	}

	public Result gen(SimplePredicate l, int index, boolean parallelize, Map<Var, CppExpr> env) {
		return gen1(l, index, parallelize, env);
	}

	public Result gen(Assignment l, Map<Var, CppExpr> env) {
		return gen1(l, -1, false, env);
	}

	public Result gen(Destructor l, Map<Var, CppExpr> env) {
		return gen1(l, -1, false, env);
	}

	public Result gen(Check l, Map<Var, CppExpr> env) {
		return gen1(l, -1, false, env);
	}

	private Result gen1(SimpleLiteral l, int index, boolean parallelize, Map<Var, CppExpr> env) {
		return new Worker(index, parallelize, new HashMap<>(env)).go(l);
	}

	private class Worker {

		private final Map<Var, CppExpr> env;
		private final TermCodeGen tcg = new TermCodeGen(ctx);
		private final int index;
		private final boolean parallelize;

		public Worker(int index, boolean parallelize, Map<Var, CppExpr> env) {
			this.index = index;
			this.env = env;
			this.parallelize = parallelize;
		}

		public Result go(SimpleLiteral l) {
			Pair<Function<CppStmt, CppStmt>, ResultType> p = l.accept(visitor, null);
			return new Result(p.fst(), env, p.snd());
		}

		private final SimpleLiteralVisitor<Void, Pair<Function<CppStmt, CppStmt>, ResultType>> visitor = new SimpleLiteralVisitor<Void, Pair<Function<CppStmt, CppStmt>, ResultType>>() {

			@Override
			public Pair<Function<CppStmt, CppStmt>, ResultType> visit(Assignment assignment, Void input) {
				return new Pair<>(handleAssignment(assignment), ResultType.OTHER);
			}

			@Override
			public Pair<Function<CppStmt, CppStmt>, ResultType> visit(Check check, Void input) {
				return new Pair<>(handleCheck(check), ResultType.OTHER);
			}

			@Override
			public Pair<Function<CppStmt, CppStmt>, ResultType> visit(Destructor destructor, Void input) {
				return new Pair<>(handleDestructor(destructor), ResultType.OTHER);
			}

			@Override
			public Pair<Function<CppStmt, CppStmt>, ResultType> visit(SimplePredicate predicate, Void input) {
				if (predicate.isNegated()) {
					return new Pair<>(handleNegativePred(predicate), ResultType.LOOKUP);
				} else {
					return handlePositivePred(predicate);
				}
			}

		};

		private Function<CppStmt, CppStmt> handleAssignment(Assignment assignment) {
			Var x = assignment.getDef();
			Term val = assignment.getVal();
			Pair<CppStmt, CppExpr> p = tcg.gen(val, env);
			String id = ctx.newId("x");
			CppStmt def = CppDecl.mk(id, p.snd());
			CppVar var = CppVar.mk(id);
			env.put(x, var);
			return s -> CppSeq.mk(p.fst(), def, s);
		}

		private Function<CppStmt, CppStmt> handleCheck(Check check) {
			Term lhs = check.getLhs();
			Term rhs = check.getRhs();
			Pair<CppStmt, CppExpr> p1 = tcg.gen(lhs, env);
			Pair<CppStmt, CppExpr> p2 = tcg.gen(rhs, env);
			CppExpr term1 = CppMethodCall.mk(p1.snd(), "get");
			CppExpr term2 = CppMethodCall.mk(p2.snd(), "get");
			CppExpr guard = CppFuncCall.mk("Term::compare", term1, term2);
			if (!check.isNegated()) {
				guard = CppUnop.mkNot(guard);
			}
			final CppExpr guard2 = guard;
			return s -> CppSeq.mk(p1.fst(), p2.fst(), CppIf.mk(guard2, s));
		}

		private Function<CppStmt, CppStmt> handleDestructor(Destructor destructor) {
			Pair<CppStmt, CppExpr> p = tcg.gen(destructor.getScrutinee(), env);
			CppExpr base = p.snd();
			CppVar sym = CppVar.mk(ctx.lookupRepr(destructor.getSymbol()));
			CppExpr guard = CppBinop.mkEq(CppAccess.mkThruPtr(base, "sym"), sym);
			List<CppStmt> stmts = new ArrayList<>();
			int i = 0;
			for (Var x : destructor.getBindings()) {
				String id = ctx.newId("x");
				stmts.add(CppDecl.mkRef(id, CodeGenUtil.mkComplexTermLookup(base, i)));
				env.put(x, CppVar.mk(id));
				i++;
			}
			CppStmt assignments = CppSeq.mk(stmts);
			return s -> CppSeq.mk(p.fst(), CppIf.mk(guard, CppSeq.mk(assignments, s)));
		}

		private Function<CppStmt, CppStmt> handleNegativePred(SimplePredicate pred) {
			return mkContains(pred, true);
		}

		private Pair<Function<CppStmt, CppStmt>, ResultType> handlePositivePred(SimplePredicate pred) {
			if (!hasFreeArgs(pred)) {
				return new Pair<>(mkContains(pred, false), ResultType.LOOKUP);
			} else {
				Triple<Function<CppStmt, CppStmt>, CppExpr, ResultType> tri = genTupleIterator(pred);
				Function<CppStmt, CppStmt> loop = genLoop(pred, tri.second);
				return new Pair<>(s -> tri.first.apply(loop.apply(s)), tri.third);
			}
		}

		private boolean useHint(Relation rel) {
			return hintsEnabled && hints.contains(rel);
		}

		private Function<CppStmt, CppStmt> mkContains(SimplePredicate pred, boolean isNegated) {
			Pair<CppStmt, CppExpr> key = genKey(pred);
			Relation rel = ctx.lookupRelation(pred.getSymbol());
			CppExpr guard = rel.mkContains(index, key.snd(), useHint(rel));
			if (isNegated) {
				guard = CppUnop.mkNot(guard);
			}
			final CppExpr guard2 = guard;
			return s -> CppSeq.mk(key.fst(), CppIf.mk(guard2, s));
		}

		private boolean hasFreeArgs(SimplePredicate pred) {
			for (BindingType ty : pred.getBindingPattern()) {
				if (ty == BindingType.FREE) {
					return true;
				}
			}
			return false;
		}

		private Triple<Function<CppStmt, CppStmt>, CppExpr, ResultType> genTupleIterator(SimplePredicate pred) {
			if (parallelize) {
				Pair<Function<CppStmt, CppStmt>, CppExpr> p = genParallelLoop(pred);
				return new Triple<>(p.fst(), p.snd(), ResultType.PARALLEL_LOOP);
			} else {
				Pair<Function<CppStmt, CppStmt>, CppExpr> p = genNormalLookup(pred);
				return new Triple<>(p.fst(), p.snd(), ResultType.LOOP);
			}
		}

		private Pair<Function<CppStmt, CppStmt>, CppExpr> genParallelLoop(SimplePredicate pred) {
			Pair<Function<CppStmt, CppStmt>, String> p = genPartition(pred);
			String part = p.snd();
			CppVar it = CppVar.mk("it");
			// The for loop needs to follow a particular form to be picked up by OpenMP
			CppExpr init = ExprFromString.mk(part + ".begin()");
			CppExpr guard = ExprFromString.mk("it < " + part + ".end()");
			CppExpr update = ExprFromString.mk("++it");
			CppStmt decls = mkContextDeclarations();
			Function<CppStmt, CppStmt> forLoop = body -> CppSeq.mk(CppVar.mk("PARALLEL_START").toStmt(), decls,
					CppFor.mkParallel("it", init, guard, update, body), CppVar.mk("PARALLEL_END").toStmt());
			return new Pair<>(body -> p.fst().apply(forLoop.apply(body)), CppUnop.mkDeref(it));
		}

		private CppStmt mkContextDeclarations() {
			List<CppStmt> stmts = new ArrayList<>();
			for (Relation rel : hints) {
				stmts.add(rel.mkDeclContext());
			}
			return CppSeq.mk(stmts);
		}

		private Pair<Function<CppStmt, CppStmt>, String> genPartition(SimplePredicate pred) {
			if (!containsBoundPosition(pred.getBindingPattern())) {
				CppStmt assign = CppDecl.mk("part", lookupRelation(pred).mkPartition());
				return new Pair<>(s -> CppSeq.mk(assign, s), "part");
			} else {
				Pair<Function<CppStmt, CppStmt>, CppExpr> p = genNormalLookup(pred);
				CppStmt assign = CppDecl.mk("part", CppMethodCall.mk(p.snd(), "partition"));
				return new Pair<>(s -> p.fst().apply(CppSeq.mk(assign, s)), "part");
			}
		}

		private boolean containsBoundPosition(BindingType[] pat) {
			for (BindingType binding : pat) {
				if (binding == BindingType.BOUND) {
					return true;
				}
			}
			return false;
		}

		private Pair<CppStmt, CppExpr> genKey(SimplePredicate pred) {
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
			return new Pair<>(CppSeq.mk(stmts), tup);
		}

		private Pair<Function<CppStmt, CppStmt>, CppExpr> genNormalLookup(SimplePredicate pred) {
			Pair<CppStmt, CppExpr> p = genKey(pred);
			Relation rel = ctx.lookupRelation(pred.getSymbol());
			CppExpr call = rel.mkLookup(index, Arrays.asList(pred.getBindingPattern()), p.snd(), useHint(rel));
			return new Pair<>(s -> CppSeq.mk(p.fst(), s), call);
		}

		private Function<CppStmt, CppStmt> genLoop(SimplePredicate pred, CppExpr it) {
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

	public static enum ResultType {
		LOOKUP, LOOP, PARALLEL_LOOP, OTHER;
	}

	public static class Result {

		private final Function<CppStmt, CppStmt> k;
		private final Map<Var, CppExpr> newEnv;
		private final ResultType resType;

		private Result(Function<CppStmt, CppStmt> k, Map<Var, CppExpr> newEnv, ResultType resType) {
			this.k = k;
			this.newEnv = newEnv;
			this.resType = resType;
		}

		public Function<CppStmt, CppStmt> getK() {
			return k;
		}

		public Map<Var, CppExpr> getNewEnv() {
			return newEnv;
		}

		public ResultType getResType() {
			return resType;
		}

	}

}
