package edu.harvard.seas.pl.formulog.eval;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.AtomVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb.IndexedFactDBBuilder;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.smt.Z3ThreadFactory;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbolFactory.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.CountingFJPImpl;
import edu.harvard.seas.pl.formulog.util.MockCountingFJP;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Validator;
import edu.harvard.seas.pl.formulog.validating.ast.ValidProgram;

public class StratifiedEvaluation implements Evaluation {

	private static final boolean softExceptions = System.getProperty("softExceptions") != null;
	private static final boolean factTrace = System.getProperty("factTrace") != null;
	private static final boolean sequential = System.getProperty("sequential") != null;

	private final ValidProgram prog;
	private EvaluationResult res;

	private StratifiedEvaluation(ValidProgram prog) {
		this.prog = prog;
	}

	public static StratifiedEvaluation setup(WellTypedProgram prog, boolean useDemandTransformation)
			throws InvalidProgramException {
		Program magicProg = (new MagicSetTransformer(prog)).transform(useDemandTransformation, true);
		ValidProgram vprog = (new Validator(magicProg)).validate();
		return new StratifiedEvaluation(vprog);
	}

	public ValidProgram getProgram() {
		return prog;
	}

	public synchronized void run() throws EvaluationException {
		run(Runtime.getRuntime().availableProcessors());
	}

	public synchronized void run(int nthreads) throws EvaluationException {
		if (res == null) {
			for (int i = 0; i < prog.getNumberOfStrata(); ++i) {
				if (prog.getStratum(i).hasRecursiveNegationOrAggregation()) {
					throw new EvaluationException(
							"This interpreter cannot evaluate a program with recursive negation or aggregation");
				}
			}
			Eval e = new Eval(nthreads);
			EvaluationException exception = null;
			IndexedFactDb db;
			try {
				db = e.eval();
			} catch (EvaluationException exn) {
				db = e.db;
				exception = exn;
			}
			final IndexedFactDb finalDb = db;
			res = makeEvaluationResult(db);
			if (exception != null) {
				throw exception;
			}
		}
	}

	private EvaluationResult makeEvaluationResult(IndexedFactDb db) {
		Set<NormalAtom> ans = null;
		if (prog.hasQuery()) {
			NormalAtom q = prog.getQuery();
			ans = new HashSet<>();
			try {
				for (NormalAtom a : db.query(q.getSymbol())) {
					if (Unification.unify(a, q, new SimpleSubstitution())) {
						ans.add(a);
					}
				}
			} catch (EvaluationException e) {
				throw new AssertionError("impossible");
			}
		}
		Set<NormalAtom> ans2 = Collections.unmodifiableSet(ans);
		return new EvaluationResult() {

			@Override
			public Set<NormalAtom> getAll(Symbol sym) {
				return Collections.unmodifiableSet(db.query(sym));
			}

			@Override
			public Set<NormalAtom> getQueryAnswer() {
				return ans2;
			}

			@Override
			public Set<Symbol> getSymbols() {
				return Collections.unmodifiableSet(db.getSymbols());
			}

		};
	}

	public EvaluationResult getResult() {
		if (res == null) {
			throw new IllegalStateException("Must run evaluation before requesting result.");
		}
		return res;
	}

	private class Eval {
		private final Map<Integer, Map<Symbol, Set<IndexedRule>>> rules = new ConcurrentHashMap<>();
		private final Map<Integer, Set<IndexedRule>> specialRules = new ConcurrentHashMap<>();
		private final Map<Integer, Set<Symbol>> triggers = new ConcurrentHashMap<>();
		private final Map<IndexedRule, RuleSubstitution> substitutions = new ConcurrentHashMap<>();
		private volatile int curStratum;
		private final CountingFJP<EvaluationException> exec;
		private final IndexedFactDb db;

		public Eval(int nthreads) throws EvaluationException {
			if (sequential) {
				exec = new MockCountingFJP<>();
			} else {
				exec = new CountingFJPImpl<>(nthreads, new Z3ThreadFactory(prog.getSymbolManager()));
			}
			db = preprocessRules();
			processInitFacts();
		}

		public IndexedFactDb eval() throws EvaluationException {
			for (; curStratum < prog.getNumberOfStrata(); ++curStratum) {
				for (IndexedRule r : Util.lookupOrCreate(specialRules, curStratum, () -> Util.concurrentSet())) {
					exec.externallyAddTask(new SpecialWorkItem(r, getSubstitution(r)));
				}
				for (Symbol sym : Util.lookupOrCreate(triggers, curStratum, () -> Util.concurrentSet())) {
					for (IndexedRule r : lookupRulesInCurStratum(sym)) {
						for (Atom fact : db.query(sym)) {
							exec.externallyAddTask(new WorkItem(fact, r, getSubstitution(r)));
						}
					}
				}
				exec.blockUntilFinished();
			}
			exec.shutdown();
			if (exec.hasFailed()) {
				throw exec.getFailureCause();
			}
			return db;
		}

		private void processInitFacts() throws EvaluationException {
			for (Symbol sym : prog.getFactSymbols()) {
				for (Atom a : prog.getFacts(sym)) {
					db.add((NormalAtom) a);
				}
			}
		}

		private IndexedFactDb preprocessRules() {
			IndexedFactDBBuilder dbb = new IndexedFactDBBuilder(prog);
			RulePreprocessor pp = new RulePreprocessor();
			AtomPreprocessor ap = new AtomPreprocessor();
			for (Symbol sym : prog.getRuleSymbols()) {
				for (Rule r : prog.getRules(sym)) {
					int stratum = prog.getStratumRank(r.getHead().getSymbol());
					for (BasicRule q : pp.preprocess(r, prog)) {
						IndexedRule indexed = new IndexedRule(q, dbb);
						Atom first = indexed.getBody(0);
						Symbol firstSym = first.getSymbol();
						if (firstSym.getSymbolType().equals(SymbolType.SPECIAL_REL) || first.isNegated()) {
							Util.lookupOrCreate(specialRules, stratum, () -> Util.concurrentSet()).add(indexed);
						} else {
							Util.lookupOrCreate(triggers, stratum, () -> Util.concurrentSet()).add(firstSym);
							lookupRules(stratum, firstSym).add(indexed);
						}
						substitutions.put(indexed, new RuleSubstitution(indexed));
						for (Atom a : indexed.getBody()) {
							ap.preprocess(a);
						}
					}
				}
			}
			return dbb.build();
		}

		private class AtomPreprocessor {
			private final Set<Symbol> visitedFunctions = new HashSet<>();

			public void preprocess(Atom a) {
				for (Term arg : a.getArgs()) {
					preprocessTerm(arg);
				}
			}

			private void preprocessExpr(Expr e) {
				e.visit(new ExprVisitor<Void, Void>() {

					@Override
					public Void visit(MatchExpr matchExpr, Void in) {
						preprocessTerm(matchExpr.getMatchee());
						for (MatchClause cl : matchExpr.getClauses()) {
							preprocessTerm(cl.getLhs());
							preprocessTerm(cl.getRhs());
						}
						return null;
					}

					@Override
					public Void visit(FunctionCall function, Void in) {
						for (Term arg : function.getArgs()) {
							preprocessTerm(arg);
						}
						Symbol funcSym = function.getSymbol();
						if (!visitedFunctions.contains(funcSym)) {
							visitedFunctions.add(funcSym);
							if (funcSym instanceof PredicateFunctionSymbol) {
								makeFunctionForPredicate((PredicateFunctionSymbol) funcSym);
							} else if (prog.getDef(funcSym) instanceof CustomFunctionDef) {
								CustomFunctionDef def = (CustomFunctionDef) prog.getDef(funcSym);
								preprocessTerm(def.getBody());
							}
						}
						return null;
					}
				}, null);
			}

			private void makeFunctionForPredicate(PredicateFunctionSymbol sym) {
				DummyFunctionDef def = (DummyFunctionDef) prog.getDef(sym);
				if (def.getDef() == null) {
					if (sym.isReification()) {
						makeReifyPredicate(sym, def);
					} else {
						makeQueryPredicate(sym, def);
					}
				}
			}

			private void makeReifyPredicate(PredicateFunctionSymbol sym, DummyFunctionDef def) {
				Symbol predSym = sym.getPredicateSymbol();
				int arity = predSym.getArity();
				Symbol tupSym = (arity > 1) ? prog.getSymbolManager().lookupTupleSymbol(arity) : null;
				def.setDef(new FunctionDef() {

					@Override
					public Symbol getSymbol() {
						return predSym;
					}

					@Override
					public Term evaluate(Term[] args) throws EvaluationException {
						Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
						for (NormalAtom fact : db.query(predSym)) {
							Term tuple = makeTuple(fact.getArgs());
							t = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { tuple, t });
						}
						return t;
					}

					private Term makeTuple(Term[] args) {
						if (tupSym == null) {
							return args[0];
						} else {
							return Constructors.make(tupSym, args);
						}
					}

				});
			}

			private void makeQueryPredicate(PredicateFunctionSymbol sym, DummyFunctionDef def) {
				Symbol predSym = sym.getPredicateSymbol();
				def.setDef(new FunctionDef() {

					@Override
					public Symbol getSymbol() {
						return def.getSymbol();
					}

					@Override
					public Term evaluate(Term[] args) throws EvaluationException {
						NormalAtom fact = (NormalAtom) Atoms.getPositive(predSym, args);
						if (db.hasFact(fact)) {
							return Constructors.trueTerm();
						} else {
							return Constructors.falseTerm();
						}
					}

				});
			}

			private void preprocessTerm(Term t) {
				t.visit(new TermVisitor<Void, Void>() {

					@Override
					public Void visit(Var t, Void in) {
						return null;
					}

					@Override
					public Void visit(Constructor t, Void in) {
						for (Term arg : t.getArgs()) {
							arg.visit(this, null);
						}
						return null;
					}

					@Override
					public Void visit(Primitive<?> prim, Void in) {
						return null;
					}

					@Override
					public Void visit(Expr expr, Void in) {
						preprocessExpr(expr);
						return null;
					}

				}, null);
			}
		}

		private RuleSubstitution getSubstitution(IndexedRule r) {
			return substitutions.get(r).fresh();
		}

		private Set<IndexedRule> lookupRulesInCurStratum(Symbol sym) {
			return lookupRules(curStratum, sym);
		}

		private Set<IndexedRule> lookupRules(int stratum, Symbol sym) {
			Map<Symbol, Set<IndexedRule>> r = Util.lookupOrCreate(rules, stratum, () -> new ConcurrentHashMap<>());
			return Util.lookupOrCreate(r, sym, () -> Util.concurrentSet());
		}

		@SuppressWarnings("serial")
		private class WorkItem extends AbstractWorkItem {

			private final Atom trigger;

			private WorkItem(Atom trigger, IndexedRule rule, RuleSubstitution s) {
				super(rule, s);
				this.trigger = trigger;
			}

			public void doTask() {
				try {
					Atom first = rule.getBody(0);
					if (first.isNegated() || first.getSymbol().getSymbolType().equals(SymbolType.SPECIAL_REL)) {
						throw new AssertionError();
					} else {
						if (!Unification.unify(trigger, first, s)) {
							return;
						}
					}
					super.doTask();
				} catch (EvaluationException e) {
					if (softExceptions) {
						return;
					}
					exec.fail(e);
				}
			}

		}

		@SuppressWarnings("serial")
		private class SpecialWorkItem extends AbstractWorkItem {

			private SpecialWorkItem(IndexedRule rule, RuleSubstitution s) {
				super(rule, s);
			}

			public void doTask() {
				try {
					Atom first = rule.getBody(0);
					boolean success = first.visit(new AtomVisitorExn<Void, Boolean, EvaluationException>() {

						@Override
						public Boolean visit(NormalAtom normalAtom, Void in) throws EvaluationException {
							assert normalAtom.isNegated();
							return handleNegated(normalAtom, rule.getDBIndex(0), true);
						}

						@Override
						public Boolean visit(UnifyAtom unifyAtom, Void in) throws EvaluationException {
							return handleUnifyAtom(unifyAtom, true);
						}

					}, null);
					if (!success) {
						return;
					}
					super.doTask();
				} catch (EvaluationException e) {
					if (softExceptions) {
						return;
					}
					exec.fail(e);
				}
			}
		}

		@SuppressWarnings("serial")
		private abstract class AbstractWorkItem extends AbstractFJPTask<EvaluationException> {

			protected final IndexedRule rule;
			protected final RuleSubstitution s;

			protected AbstractWorkItem(IndexedRule rule, RuleSubstitution s) {
				super(exec);
				this.rule = rule;
				this.s = s;
			}

			public void doTask() {
				try {
					int pos = 1;
					Deque<Iterator<NormalAtom>> stack = new ArrayDeque<>();
					boolean goingDown = true;
					do {
						try {
							if (pos >= rule.getBodySize()) {
								reportFacts(s);
								--pos;
								goingDown = false;
							} else {
								s.setToBefore(pos);
								Integer dbidx = rule.getDBIndex(pos);
								Atom curAtom = rule.getBody(pos);
								if (curAtom instanceof NormalAtom) {
									if (curAtom.isNegated()) {
										goingDown = handleNegated((NormalAtom) curAtom, dbidx, goingDown);
									} else {
										goingDown = handlePositive((NormalAtom) curAtom, dbidx, goingDown, stack);
									}
								} else if (curAtom instanceof UnifyAtom) {
									goingDown = handleUnifyAtom((UnifyAtom) curAtom, goingDown);
								} else {
									throw new AssertionError();
								}
								if (goingDown) {
									++pos;
								} else {
									--pos;
								}
							}
						} catch (EvaluationException e) {
							if (softExceptions) {
								--pos;
								goingDown = false;
							} else {
								throw e;
							}
						}
					} while (pos > 0);
				} catch (EvaluationException e) {
					exec.fail(e);
				}
			}

			protected boolean handleUnifyAtom(UnifyAtom atom, boolean goingDown) throws EvaluationException {
				if (goingDown) {
					return Unification.unify(atom.getArgs()[0], atom.getArgs()[1], s) ^ atom.isNegated();
				}
				return false;
			}

			protected boolean handleNegated(NormalAtom curAtom, int dbidx, boolean goingDown)
					throws EvaluationException {
				return goingDown && !db.query(dbidx, s).iterator().hasNext();
			}

			private boolean handlePositive(NormalAtom curAtom, int dbidx, boolean goingDown,
					Deque<Iterator<NormalAtom>> stack) throws EvaluationException {
				Iterator<NormalAtom> it;
				if (goingDown) {
					it = db.query(dbidx, s).iterator();
					stack.push(it);
				} else {
					it = stack.peek();
				}
				if (it.hasNext()) {
					NormalAtom next = it.next();
					Unification.unsafeUnifyWithFact(curAtom, next, s);
					return true;
				} else {
					stack.pop();
					return false;
				}
			}

			private void reportFacts(RuleSubstitution s) throws EvaluationException {
				Atom a = rule.getHead();
				Atom fact = Atoms.normalize(a, s);
				boolean isNew = db.add((NormalAtom) fact);
				if (isNew) {
					if (factTrace) {
						String msg = "\nBEGIN NEW FACT\nFact:\n";
						msg += fact;
						msg += "\n\nDerived using this rule:\n" + rule;
						msg += "\n\nUnder this substitution:\n" + s.toSimpleString();
						msg += "\nEND NEW FACT";
						System.err.println(msg);
					}
					for (IndexedRule r : lookupRulesInCurStratum(fact.getSymbol())) {
						exec.recursivelyAddTask(new WorkItem(fact, r, getSubstitution(r)));
					}
				}
			}

		}

	}

}
