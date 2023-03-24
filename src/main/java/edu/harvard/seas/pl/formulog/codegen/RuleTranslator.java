package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.Configuration;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.*;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.*;

import java.util.*;
import java.util.stream.Collectors;

public class RuleTranslator {

	private final CodeGenContext ctx;
	private final QueryPlanner queryPlanner;
	private static final String checkPred = "CODEGEN_CHECK";

	public RuleTranslator(CodeGenContext ctx, QueryPlanner queryPlanner) {
		this.ctx = ctx;
		this.queryPlanner = queryPlanner;
	}

	public Pair<List<SRule>, List<Stratum>> translate(BasicProgram prog) throws CodeGenException {
		var strats = checkStratification(prog);
		List<SRule> l = new ArrayList<>();
		Worker worker = new Worker(prog);
		for (var stratum : strats) {
			for (RelationSymbol sym : stratum.getPredicateSyms()) {
				for (BasicRule r : prog.getRules(sym)) {
					var sr = worker.translate(r);
					sr.setQueryPlan(queryPlanner.genPlan(sr, stratum));
					l.add(sr);
				}
			}
		}
		l.addAll(worker.createProjectionRules());
		l.add(worker.createCheckRule());
		return new Pair<>(l, strats);
	}

	private List<Stratum> checkStratification(BasicProgram prog) throws CodeGenException {
		Stratifier stratifier = new Stratifier(prog);
		List<Stratum> strats;
		try {
			strats = stratifier.stratify();
		} catch (InvalidProgramException e) {
			throw new CodeGenException(e);
		}
		for (Stratum strat : strats) {
			if (strat.hasRecursiveNegationOrAggregation()) {
				throw new CodeGenException("Cannot handle recursive negation or aggregation: " + strat);
			}
		}
		return strats;
	}

	private class Worker {

		private final BasicProgram prog;
		private Map<Var, Integer> varCount;
		private final Set<Pair<RelationSymbol, List<Boolean>>> projections = new HashSet<>();

		public Worker(BasicProgram prog) {
			this.prog = prog;
		}

		private SRule translate(BasicRule br) throws CodeGenException {
			SimpleRule sr;
			try {
				ValidRule vr = ValidRule.make(br, (_lit, _vars) -> 1);
				sr = SimpleRule.make(vr, prog.getFunctionCallFactory());
				varCount = sr.countVariables();
			} catch (InvalidProgramException e) {
				throw new CodeGenException(e);
			}
			List<SLit> headTrans = translate(sr.getHead());
			assert headTrans.size() == 1;
			SLit head = headTrans.get(0);
			List<SLit> body = new ArrayList<>();
			for (int i = 0; i < sr.getBodySize(); ++i) {
				body.addAll(translate(sr.getBody(i)));
			}
			return new SRule(head, body);
		}

		private List<SLit> translate(SimpleLiteral lit) {
			return lit.accept(new SimpleLiteralVisitor<Void, List<SLit>>() {
				@Override
				public List<SLit> visit(Assignment assignment, Void input) {
					STerm lhs = translate(assignment.getDef());
					STerm rhs = translate(assignment.getVal());
					return Collections.singletonList(new SInfixBinaryOpAtom(lhs, "=", rhs));
				}

				@Override
				public List<SLit> visit(Check check, Void input) {
					STerm lhs = translate(check.getLhs());
					STerm rhs = translate(check.getRhs());
					return Collections.singletonList(new SInfixBinaryOpAtom(lhs, check.isNegated() ? "!=" : "=", rhs));
				}

				@Override
				public List<SLit> visit(Destructor destructor, Void input) {
					/*
					 * A destructor of the form
					 * 
					 * t -> c(X1, ..., Xn)
					 * 
					 * gets translated as
					 * 
					 * X0 = [[t]],
					 * 
					 * @dtor_c(X0) = B, CODEGEN_CHECK(B, B2), X1 = @nth(0, X0, B2), ..., Xn = @nth(n
					 * - 1, X0, B2).
					 * 
					 * @dtor_c(...) returns 1 if the term has the symbol c and 0 otherwise.
					 * CODEGEN_CHECK has a single tuple [1, 1]. It is there to make sure that the
					 * destructor has been successful before nth is called.
					 */
					List<SLit> l = new ArrayList<>();
					Term scrutinee = destructor.getScrutinee();
					STerm translatedScrutineeExpr = translate(scrutinee);
					Var scrutineeVar = Var.fresh();
					STerm translatedScrutineeVar = new SVar(scrutineeVar);
					l.add(new SInfixBinaryOpAtom(translatedScrutineeVar, "=", translatedScrutineeExpr));
					List<Var> args = Collections.singletonList(scrutineeVar);
					String functor = ctx.lookupOrCreateFunctorName(destructor.getSymbol());
					var dtor = new SDestructorBody(args, scrutineeVar, destructor.getSymbol());
					ctx.registerFunctorBody(functor, dtor);
					List<STerm> translatedArgs = args.stream().map(Worker.this::translate).collect(Collectors.toList());
					assert translatedArgs.size() == 1 && translatedArgs.get(0) instanceof SVar;
					STerm lhs = new SFunctorCall(functor, translatedArgs);
					SVar recRef = new SVar(Var.fresh());
					l.add(new SInfixBinaryOpAtom(lhs, "=", recRef));
					SVar checkOutput = new SVar(Var.fresh());
					l.add(new SAtom(checkPred, Arrays.asList(recRef, checkOutput), false));
					int arity = destructor.getSymbol().getArity();
					Var[] bindings = destructor.getBindings();
					for (int i = 0; i < arity; ++i) {
						SFunctorCall call = new SFunctorCall("nth", new SInt(i), translatedArgs.get(0), checkOutput);
						l.add(new SInfixBinaryOpAtom(translate(bindings[i]), "=", call));
					}
					return l;
				}

				@Override
				public List<SLit> visit(SimplePredicate predicate, Void input) {
					List<STerm> args = Arrays.stream(predicate.getArgs()).map(Worker.this::translate)
							.collect(Collectors.toList());
					SLit lit;
					if (predicate.isNegated()) {
						lit = handleNegatedPredicate(predicate, args);
					} else {
						String symbol = ctx.lookupRepr(predicate.getSymbol());
						lit = new SAtom(symbol, args, false);
					}
					return Collections.singletonList(lit);
				}
			}, null);
		}

		private SLit handleNegatedPredicate(SimplePredicate predicate, List<STerm> souffleArgs) {
			List<Boolean> projection = new ArrayList<>();
			int ignoredCount = 0;
			var args = predicate.getArgs();
			for (Term arg : args) {
				if (arg instanceof Var && varCount.get((Var) arg) == 1) {
					ignoredCount++;
					projection.add(false);
				} else {
					projection.add(true);
				}
			}
			RelationSymbol sym = predicate.getSymbol();
			if (ignoredCount == 0) {
				return new SAtom(ctx.lookupRepr(sym), souffleArgs, true);
			}
			projections.add(new Pair<>(predicate.getSymbol(), projection));
			List<STerm> newArgs = new ArrayList<>();
			for (int i = 0; i < souffleArgs.size(); ++i) {
				if (projection.get(i)) {
					newArgs.add(souffleArgs.get(i));
				}
			}
			return new SAtom(createProjectionSymbol(sym, projection), newArgs, true);
		}

		private String createProjectionSymbol(RelationSymbol sym, List<Boolean> projection) {
			StringBuilder sb = new StringBuilder();
			sb.append("CODEGEN_PROJECT_");
			sb.append(ctx.lookupRepr(sym));
			for (Boolean retain : projection) {
				sb.append(retain ? "1" : "0");
			}
			return sb.toString();
		}

		private SFunctorCall liftToFunctor(Term t) {
			String functor = ctx.lookupOrCreateFunctorName(t);
			List<Var> args = new ArrayList<>(t.varSet());
			ctx.registerFunctorBody(functor, new SExprBody(args, t));
			List<STerm> translatedArgs = args.stream().map(this::translate).collect(Collectors.toList());
			return new SFunctorCall(functor, translatedArgs);
		}

		private STerm translate(Term t) {
			return t.accept(new Terms.TermVisitor<Void, STerm>() {
				@Override
				public STerm visit(Var t, Void in) {
					return new SVar(t);
				}

				@Override
				public STerm visit(Constructor c, Void in) {
					return liftToFunctor(c);
				}

				@Override
				public STerm visit(Primitive<?> p, Void in) {
					return liftToFunctor(p);
				}

				@Override
				public STerm visit(Expr e, Void in) {
					return liftToFunctor(e);
				}
			}, null);
		}

		List<SRule> createProjectionRules() {
			List<SRule> l = new ArrayList<>();
			for (var p : projections) {
				l.add(createProjection(p.fst(), p.snd()));
			}
			return l;
		}

		private SRule createProjection(RelationSymbol sym, List<Boolean> projection) {
			List<STerm> headArgs = new ArrayList<>();
			List<STerm> bodyArgs = new ArrayList<>();
			for (int i = 0; i < sym.getArity(); ++i) {
				STerm arg = new SVar(Var.fresh("x" + i));
				bodyArgs.add(arg);
				if (projection.get(i)) {
					headArgs.add(arg);
				}
			}
			String projSym = createProjectionSymbol(sym, projection);
			SLit head = new SAtom(projSym, headArgs, false);
			SLit bodyAtom = new SAtom(ctx.lookupRepr(sym), bodyArgs, false);
			ctx.registerCustomRelation(projSym, headArgs.size(), SRuleMode.INTERMEDIATE);
			return new SRule(head, bodyAtom);
		}

		public SRule createCheckRule() {
			ctx.registerCustomRelation(checkPred, 2, SRuleMode.INTERMEDIATE);
			SLit head = new SAtom(checkPred, Arrays.asList(new SInt(1), new SInt(1)), false);
			return new SRule(head);
		}
	}

}
