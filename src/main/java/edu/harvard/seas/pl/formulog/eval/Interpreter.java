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
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.AtomVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef.Expr;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef.MatchClause;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef.TermExpr;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB.IndexedFactDBBuilder;
import edu.harvard.seas.pl.formulog.smt.Z3ThreadFactory;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbolForPredicateFactory.FunctionSymbolForPredicate;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.util.CountingFJP.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;

public class Interpreter {

	private static final boolean softExceptions = System.getProperty("softExceptions") != null;

	private final ValidProgram prog;
	private IndexedFactDB res;

	public Interpreter(ValidProgram prog) {
		this.prog = prog;
	}

	public synchronized IndexedFactDB run() throws EvaluationException {
		return run(Runtime.getRuntime().availableProcessors());
	}

	public synchronized IndexedFactDB run(int nthreads) throws EvaluationException {
		if (res == null) {
			Eval e = new Eval(nthreads);
			try {
				res = e.eval();
			} catch (EvaluationException exn) {
				res = e.db;
				throw exn;
			}
		}
		return res;
	}

	public synchronized IndexedFactDB getResult() {
		return res;
	}

	private class Eval {
		private final Map<Integer, Map<Symbol, Set<IndexedRule>>> rules = new ConcurrentHashMap<>();
		private final Map<Integer, Set<IndexedRule>> specialRules = new ConcurrentHashMap<>();
		private final Map<Integer, Set<Symbol>> triggers = new ConcurrentHashMap<>();
		private final Map<IndexedRule, RuleSubstitution> substitutions = new ConcurrentHashMap<>();
		private volatile int curStratum;
		private final CountingFJP<EvaluationException> exec;
		private final IndexedFactDB db;

		public Eval(int nthreads) {
			exec = new CountingFJP<>(nthreads, new Z3ThreadFactory(prog.getSymbolManager()));
			db = preprocessRules();
			processInitFacts();
		}

		public IndexedFactDB eval() throws EvaluationException {
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

		private void processInitFacts() {
			for (Symbol sym : prog.getFactSymbols()) {
				for (Atom a : prog.getFacts(sym)) {
					db.add((NormalAtom) a);
				}
			}
		}

		private IndexedFactDB preprocessRules() {
			IndexedFactDBBuilder dbb = new IndexedFactDBBuilder();
			RulePreprocessor pp = new RulePreprocessor();
			AtomPreprocessor ap = new AtomPreprocessor(dbb);
			for (Symbol sym : prog.getRuleSymbols()) {
				for (Rule r : prog.getRules(sym)) {
					/*
					 * If the rule has multiple head atoms, associate the rule with the lowest
					 * stratum represented by one of the head atoms. It would be incorrect to
					 * evaluate the rule at a higher stratum. For instance, consider the following
					 * program: "a(0), b :- c. d :- !b. a(42) :- !d. c." The fact "a(42)" would not
					 * be derived if the rule "a(0), b :- c." were evaluated at the stratum of "a"
					 * instead of the lower stratum of "b".
					 */
					int stratum = Integer.MAX_VALUE;
					for (Atom a : r.getHead()) {
						stratum = Math.min(stratum, prog.getStratumRank(a.getSymbol()));
					}
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
			private final IndexedFactDBBuilder dbb;
			private final Set<Symbol> visitedFunctions = new HashSet<>();

			public AtomPreprocessor(IndexedFactDBBuilder dbb) {
				this.dbb = dbb;
			}

			public void preprocess(Atom a) {
				for (Term arg : a.getArgs()) {
					preprocessTerm(arg);
				}
			}

			private void preprocessExpr(Expr e) {
				e.visit(new ExprVisitor<Void, Void>() {

					@Override
					public Void visit(TermExpr termExpr, Void in) {
						preprocessTerm(termExpr.getTerm());
						return null;
					}

					@Override
					public Void visit(MatchExpr matchExpr, Void in) {
						matchExpr.getExpr().visit(this, null);
						for (MatchClause cl : matchExpr.getClauses()) {
							preprocessTerm(cl.getLHS());
							cl.getRHS().visit(this, null);
						}
						return null;
					}

				}, null);
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
					public Void visit(FunctionCall function, Void in) {
						for (Term arg : function.getArgs()) {
							arg.visit(this, null);
						}
						Symbol funcSym = function.getSymbol();
						if (!visitedFunctions.contains(funcSym)) {
							visitedFunctions.add(funcSym);
							if (funcSym instanceof FunctionSymbolForPredicate) {
								Symbol predSym = ((FunctionSymbolForPredicate) funcSym).getPredicateSymbol();
								DummyFunctionDef def = (DummyFunctionDef) prog.getDef(funcSym);
								assert def.getDef() == null;
								NormalAtom a = (NormalAtom) Atoms.getPositive(predSym, function.getArgs());
								final int idx = dbb.addIndex(a, Terms.varSet(function));
								Term trueBool = Constructors.makeZeroAry(BuiltInConstructorSymbol.TRUE);
								Term falseBool = Constructors.makeZeroAry(BuiltInConstructorSymbol.FALSE);
								def.setDef(new FunctionDef() {

									@Override
									public Symbol getSymbol() {
										return def.getSymbol();
									}

									@Override
									public Term evaluate(Term[] args, Substitution substitution)
											throws EvaluationException {
										Substitution s = new SimpleSubstitution();
										for (Var v : substitution.iterateKeys()) {
											s.put(v, substitution.get(v));
										}
										Unification.unify(a, Atoms.getPositive(predSym, args), s);
										Iterable<NormalAtom> facts = db.query(idx, s);
										if (facts.iterator().hasNext()) {
											return trueBool;
										} else {
											return falseBool;
										}
									}

								});
							} else if (prog.getDef(funcSym) instanceof CustomFunctionDef) {
								CustomFunctionDef def = (CustomFunctionDef) prog.getDef(funcSym);
								preprocessExpr(def.getBody());
							}
						}
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
					Unification.unsafeUnifyWithFact(curAtom, it.next(), s);
					return true;
				} else {
					stack.pop();
					return false;
				}
			}

			private void reportFacts(Substitution s) throws EvaluationException {
				for (Atom a : rule.getHead()) {
					Atom fact = Atoms.normalize(Atoms.applySubstitution(a, s));
					boolean isNew = db.add((NormalAtom) fact);
					if (isNew) {
						for (IndexedRule r : lookupRulesInCurStratum(fact.getSymbol())) {
							exec.recursivelyAddTask(new WorkItem(fact, r, getSubstitution(r)));
						}
					}
				}
			}

		}

	}

}
