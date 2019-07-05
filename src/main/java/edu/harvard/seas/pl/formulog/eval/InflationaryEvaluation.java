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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.AtomVisitor;
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
import edu.harvard.seas.pl.formulog.ast.RelationProperties;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB.IndexedFactDBBuilder;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer.InputSymbol;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer.SupSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbolFactory.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class InflationaryEvaluation {

	private final Program prog;
	private final Map<Integer, Set<IndexedRule>> safeRules = new HashMap<>();
	private final Map<Integer, Set<IndexedRule>> delayedRules = new HashMap<>();
	private final Map<Integer, Set<IndexedRule>> firstRoundRules = new HashMap<>();
	private final IndexedFactDBBuilder dbb;
	private IndexedFactDB cumulativeDb;
	private final Map<Integer, IndexedFactDB> generationalDbs = new HashMap<>();
	private Map<Integer, Map<Symbol, Map<Integer, Set<NormalAtom>>>> deltaOld = new HashMap<>();
	private Map<Integer, Map<Symbol, Map<Integer, Set<NormalAtom>>>> deltaNew = new HashMap<>();
	private int botStratum = Integer.MAX_VALUE;
	private int topStratum = 0;
	private Map<Symbol, Set<Integer>> relevantStrata = new HashMap<>();

	public InflationaryEvaluation(Program prog) {
		this.prog = prog;
		this.dbb = new IndexedFactDBBuilder(prog);
	}

	public synchronized IndexedFactDB get() throws EvaluationException {
		if (cumulativeDb != null) {
			return cumulativeDb;
		}
		preprocessRules();
		cumulativeDb = dbb.build();
		for (Symbol sym : prog.getFactSymbols()) {
			for (Atom fact : prog.getFacts(sym)) {
				cumulativeDb.add((NormalAtom) fact);
			}
		}
		evaluate();
		return cumulativeDb;
	}

	private void evaluate() throws EvaluationException {
		// for (Map.Entry<Integer, Set<IndexedRule>> e : safeRules.entrySet()) {
		// System.out.println("SAFE RULES FOR #" + e.getKey());
		// for (IndexedRule r : e.getValue()) {
		// System.out.println(r);
		// }
		// }
		// for (Map.Entry<Integer, Set<IndexedRule>> e : delayedRules.entrySet()) {
		// System.out.println("UNSAFE RULES FOR #" + e.getKey());
		// for (IndexedRule r : e.getValue()) {
		// System.out.println(r);
		// }
		// }
		// for (Map.Entry<Integer, Set<IndexedRule>> e : firstRoundRules.entrySet()) {
		// System.out.println("FIRST ROUND RULES FOR #" + e.getKey());
		// for (IndexedRule r : e.getValue()) {
		// System.out.println(r);
		// }
		// }
		boolean changed = true;
		while (changed) {
			changed = false;
			for (int i = botStratum; i <= topStratum; ++i) {
				changed |= evaluateStratumSafe(i);
			}
		}
		;
		for (int i = botStratum; i <= topStratum; ++i) {
			// System.out.println("EVALUATING STRATUM UNSAFE " + i);
			// System.out.println(cumulativeDb);
			for (IndexedRule r : delayedRules.get(i)) {
				// System.out.println(r);
				changed |= evaluate(r, 0, new RuleSubstitution(r), 0);
			}
			if (changed) {
				evaluate();
				break;
			}
		}
	}

	private boolean evaluateStratumSafe(int stratum) throws EvaluationException {
		// System.out.println("EVALUATING STRATUM SAFE " + stratum);
		// System.out.println(cumulativeDb);
		boolean changed = false;
		for (IndexedRule r : firstRoundRules.get(stratum)) {
			// System.out.println(r);
			changed |= evaluate(r, 0, new RuleSubstitution(r), 0);
		}
		boolean changedLastRound = true;
		while (changedLastRound) {
			changedLastRound = false;
			deltaOld.put(stratum, new HashMap<>(deltaNew.get(stratum)));
			deltaNew.get(stratum).clear();
			for (IndexedRule r : safeRules.get(stratum)) {
				// System.out.println(r);
				changedLastRound |= evaluate(r, 0, new RuleSubstitution(r), 0);
			}
			changed |= changedLastRound;
		}
		;
		return changed;
	}

	private boolean evaluate(IndexedRule r, int pos, RuleSubstitution s, int gen) throws EvaluationException {
		if (pos >= r.getBodySize()) {
			return reportFact((NormalAtom) r.getHead(), s, gen);
		}
		s.setToBefore(pos);
		return r.getBody(pos).visit(new AtomVisitorExn<Void, Boolean, EvaluationException>() {

			@Override
			public Boolean visit(NormalAtom normalAtom, Void in) throws EvaluationException {
				Symbol sym = normalAtom.getSymbol();
				Iterable<NormalAtom> facts;
				int dbIdx = r.getDBIndex(pos);
				if (sym instanceof SemiNaiveSymbol) {
					SemiNaiveSymbol snSym = (SemiNaiveSymbol) sym;
					switch (snSym.getSemiNaiveSymbolType()) {
					case CURRENT:
						facts = get(dbIdx, s, gen);
						break;
					case DELTA:
						assert pos == 0;
						return handleDelta(normalAtom, false);
					case DELTA_LOWER:
						assert pos == 0;
						return handleDelta(normalAtom, true);
					case PREVIOUS:
						facts = get(dbIdx, s, gen - 1);
						break;
					default:
						throw new AssertionError("impossible");
					}
				} else {
					facts = getAll(dbIdx, s);
				}
				return handleAtom(normalAtom, facts, gen);
			}

			private boolean handleDelta(NormalAtom a, boolean ignoreGen) throws EvaluationException {
				Symbol sym = stripSemiNaiveAnnotation(a.getSymbol());
				Symbol headSym = r.getHead().getSymbol();
				Map<Symbol, Map<Integer, Set<NormalAtom>>> d = deltaOld.get(getStratumRank(headSym));
				if (d == null) {
					return false;
				}
				Map<Integer, Set<NormalAtom>> m = d.get(sym);
				if (m == null) {
					return false;
				}
				a = (NormalAtom) Atoms.get(sym, a.getArgs(), a.isNegated());
				boolean changed = false;
				for (Map.Entry<Integer, Set<NormalAtom>> e : m.entrySet()) {
					int genToUse = ignoreGen ? gen : e.getKey();
					Set<NormalAtom> newAtoms = e.getValue();
					for (NormalAtom atom : newAtoms) {
						s.setToBefore(pos);
						if (Unification.unify(a, atom, s)) {
							changed |= evaluate(r, pos + 1, s, genToUse);
						}
					}
				}
				return changed;
			}

			private boolean handleAtom(NormalAtom a, Iterable<NormalAtom> facts, int gen) throws EvaluationException {
				Iterator<NormalAtom> it = facts.iterator();
				if (a.isNegated()) {
					return !it.hasNext() && evaluate(r, pos + 1, s, gen);
				} else {
					boolean changed = false;
					while (it.hasNext()) {
						s.setToBefore(pos);
						Unification.unsafeUnifyWithFact(a, it.next(), s);
						changed |= evaluate(r, pos + 1, s, gen);
					}
					return changed;
				}
			}

			@Override
			public Boolean visit(UnifyAtom unifyAtom, Void in) throws EvaluationException {
				Term[] args = unifyAtom.getArgs();
				if (unifyAtom.isNegated() ^ Unification.unify(args[0], args[1], s)) {
					return evaluate(r, pos + 1, s, gen);
				}
				return false;
			}

		}, null);
	}

	private int getStratumRank(Symbol sym) {
		if (sym.getSymbolType().isEDBSymbol()) {
			return -1;
		}
		sym = stripSemiNaiveAnnotation(sym);
		return prog.getRelationProperties(sym).getStratum().getRank();
	}

	private Iterable<NormalAtom> getAll(int idx, Substitution s) throws EvaluationException {
		return cumulativeDb.query(idx, s);
	}

	private Iterable<NormalAtom> get(int idx, Substitution s, int gen) throws EvaluationException {
		if (gen < 0) {
			return Collections.emptyList();
		}
		List<Iterator<NormalAtom>> its = new ArrayList<>();
		for (int i = 0; i <= gen; ++i) {
			IndexedFactDB db = generationalDbs.get(i);
			if (db != null) {
				its.add(db.query(idx, s).iterator());
			}
		}
		return new Iterable<NormalAtom>() {

			@Override
			public Iterator<NormalAtom> iterator() {

				return new Iterator<NormalAtom>() {

					private int pos = 0;

					@Override
					public boolean hasNext() {
						if (pos >= its.size()) {
							return false;
						}
						if (!its.get(pos).hasNext()) {
							pos++;
							return hasNext();
						}
						return true;
					}

					@Override
					public NormalAtom next() {
						Iterator<NormalAtom> it = its.get(pos);
						if (!it.hasNext()) {
							pos++;
							return next();
						}
						return it.next();
					}

				};
			}

		};
	}

	private boolean reportFact(NormalAtom atom, Substitution s, int gen) throws EvaluationException {
		NormalAtom fact = (NormalAtom) Atoms.normalize(atom, s);
		Symbol sym = stripSemiNaiveAnnotation(atom.getSymbol());
		fact = (NormalAtom) Atoms.getPositive(sym, fact.getArgs());
		if (incrementGen(sym)) {
			gen++;
		}
		// System.out.print("Discovered fact " + fact + " at generation " + gen + "...
		// ");
		RelationProperties props = prog.getRelationProperties(sym);
		if (props.isAggregated() && (fact = checkAggregateFact(fact, gen)) != null
				|| checkNonAggregateFact(fact, gen)) {
			for (Integer stratum : Util.lookupOrCreate(relevantStrata, sym, () -> Collections.emptySet())) {
				Map<Symbol, Map<Integer, Set<NormalAtom>>> d = Util.lookupOrCreate(deltaNew, stratum,
						() -> new HashMap<>());
				Map<Integer, Set<NormalAtom>> m = Util.lookupOrCreate(d, sym, () -> new HashMap<>());
				Util.lookupOrCreate(m, gen, () -> new HashSet<>()).add(fact);
			}
			generationalDbs.get(gen).add(fact);
			cumulativeDb.add(fact);
			// System.out.println("added");
			return true;
		} else {
			// System.out.println("not added");
			return false;
		}
	}

	private Symbol stripSemiNaiveAnnotation(Symbol sym) {
		if (sym instanceof SemiNaiveSymbol) {
			return ((SemiNaiveSymbol) sym).getUnderlyingSymbol();
		}
		return sym;
	}

	private boolean incrementGen(Symbol sym) {
		return !(sym instanceof InputSymbol || sym instanceof SupSymbol);
	}

	private boolean checkNonAggregateFact(NormalAtom fact, int gen) {
		for (int i = 0; i <= gen; ++i) {
			IndexedFactDB db = Util.lookupOrCreate(generationalDbs, i, () -> dbb.build());
			if (db.hasFact(fact)) {
				return false;
			}
		}
		return true;
	}

	private NormalAtom checkAggregateFact(NormalAtom fact, int gen) {
		throw new UnsupportedOperationException("can't handle aggregates yet");
	}

	private void preprocessRules() {
		SemiNaiveEvalPreprocessor semiNaivePreprocessor = new SemiNaiveEvalPreprocessor();
		for (Symbol sym : prog.getRuleSymbols()) {
			for (Rule r : prog.getRules(sym)) {
				semiNaivePreprocessor.preprocess(r);
			}
		}
	}

	private class SemiNaiveEvalPreprocessor {

		private final Set<Symbol> visitedFunctions = new HashSet<>();

		public void preprocess(Rule original) {
			boolean safe = checkSafetyAndSetDummyFunctions(original);
			Symbol headSym = original.getHead().getSymbol();
			int stratum = prog.getRelationProperties(headSym).getStratum().getRank();
			recordStratum(stratum);
			for (Rule semiNaiveRule : makeSemiNaiveRules(original, stratum, safe)) {
				IndexedRule indexedRule = new IndexedRule(semiNaiveRule, dbb);
				Map<Integer, Set<IndexedRule>> m;
				if (safe) {
					if (isFirstRoundRule(indexedRule, stratum)) {
						m = firstRoundRules;
					} else {
						m = safeRules;
					}
				} else {
					m = delayedRules;
				}
				m.get(stratum).add(indexedRule);
			}
		}

		private void recordStratum(int stratum) {
			safeRules.putIfAbsent(stratum, new HashSet<>());
			delayedRules.putIfAbsent(stratum, new HashSet<>());
			firstRoundRules.putIfAbsent(stratum, new HashSet<>());
			deltaOld.putIfAbsent(stratum, new HashMap<>());
			deltaNew.putIfAbsent(stratum, new HashMap<>());
			topStratum = Math.max(topStratum, stratum);
			botStratum = Math.min(botStratum, stratum);
		}

		private boolean allVars(Term[] ts) {
			for (Term t : ts) {
				if (!(t instanceof Var)) {
					return false;
				}
			}
			return true;
		}

		private boolean isFirstRoundRule(Rule r, int stratum) {
			for (Atom a : r.getBody()) {
				Symbol sym = a.getSymbol();
				if (!sym.getSymbolType().isIDBSymbol()) {
					continue;
				}
				int i = getStratumRank(sym);
				if (stratum <= i) {
					return false;
				}
			}
			return true;
		}

		private boolean checkSafetyAndSetDummyFunctions(Rule r) {
			boolean ok = true;
			for (Atom a : r.getBody()) {
				ok &= preprocess(a);
			}
			return ok;
		}

		private boolean preprocess(Atom a) {
			return a.visit(new AtomVisitor<Void, Boolean>() {

				@Override
				public Boolean visit(NormalAtom normalAtom, Void in) {
					assert allVars(normalAtom.getArgs());
					boolean notOk = normalAtom.isNegated();
					Symbol sym = normalAtom.getSymbol();
					notOk |= prog.getRelationProperties(sym).isAggregated();
					return !notOk;
				}

				@Override
				public Boolean visit(UnifyAtom unifyAtom, Void in) {
					boolean ok = true;
					for (Term t : unifyAtom.getArgs()) {
						ok &= preprocess(t);
					}
					return ok;
				}

			}, null);
		}

		private boolean preprocess(Term t) {
			return t.visit(new TermVisitor<Void, Boolean>() {

				@Override
				public Boolean visit(Var t, Void in) {
					return true;
				}

				@Override
				public Boolean visit(Constructor c, Void in) {
					boolean ok = true;
					for (Term t : c.getArgs()) {
						ok &= preprocess(t);
					}
					return ok;
				}

				@Override
				public Boolean visit(Primitive<?> p, Void in) {
					return true;
				}

				@Override
				public Boolean visit(Expr e, Void in) {
					return e.visit(new ExprVisitor<Void, Boolean>() {

						@Override
						public Boolean visit(MatchExpr matchExpr, Void in) {
							boolean ok = preprocess(matchExpr.getMatchee());
							for (MatchClause cl : matchExpr.getClauses()) {
								ok &= preprocess(cl.getRhs());
							}
							return ok;
						}

						@Override
						public Boolean visit(FunctionCall funcCall, Void in) {
							Symbol sym = funcCall.getSymbol();
							if (!visitedFunctions.add(sym)) {
								return true;
							}
							FunctionDef def = prog.getDef(sym);
							if (sym instanceof PredicateFunctionSymbol) {
								DummyFunctionDef dummy = (DummyFunctionDef) def;
								setPredicateFunction(dummy);
							}
							if (def instanceof CustomFunctionDef) {
								return preprocess(((CustomFunctionDef) def).getBody());
							}
							return true;
						}

					}, null);
				}

			}, null);
		}

		private void setPredicateFunction(DummyFunctionDef def) {
			if (def.getDef() != null) {
				return;
			}
			PredicateFunctionSymbol sym = (PredicateFunctionSymbol) def.getSymbol();
			if (sym.isReification()) {
				makeReifyPredicate(sym, def);
			} else {
				makeQueryPredicate(sym, def);
			}
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
					if (cumulativeDb.hasFact(fact)) {
						return Constructors.trueTerm();
					} else {
						return Constructors.falseTerm();
					}
				}

			});
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
					for (NormalAtom fact : cumulativeDb.query(predSym)) {
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

		private Set<Rule> makeSemiNaiveRules(Rule original, int stratum, boolean isSafe) {
			Set<Rule> rules = new HashSet<>();
			int i = 0;
			for (Atom a : original.getBody()) {
				if (shouldBeAnnotated(a, stratum, isSafe)) {
					Util.lookupOrCreate(relevantStrata, a.getSymbol(), () -> new HashSet<>()).add(stratum);
					rules.add(makeSemiNaiveRule(original, i, stratum, isSafe));
				}
				i++;
			}
			if (rules.isEmpty()) {
				return Collections.singleton(sort(original));
			}
			return rules;
		}

		private Rule makeSemiNaiveRule(Rule original, int deltaPos, int stratum, boolean isSafe) {
			List<Atom> newBody = new ArrayList<>();
			int i = 0;
			for (Atom a : original.getBody()) {
				if (shouldBeAnnotated(a, stratum, isSafe && i == deltaPos)) {
					SemiNaiveSymbolType type;
					if (i < deltaPos) {
						type = SemiNaiveSymbolType.CURRENT;
					} else if (i > deltaPos) {
						type = SemiNaiveSymbolType.PREVIOUS;
					} else if (stratum == getStratumRank(a.getSymbol())) {
						type = SemiNaiveSymbolType.DELTA;
					} else {
						type = SemiNaiveSymbolType.DELTA_LOWER;
					}
					Symbol sym = SemiNaiveSymbol.make(a.getSymbol(), type);
					newBody.add(Atoms.get(sym, a.getArgs(), a.isNegated()));
				} else {
					newBody.add(a);
				}
				i++;
			}
			Collections.swap(newBody, 0, deltaPos);
			sort(newBody);
			Rule newRule = BasicRule.get(original.getHead(), newBody);
			return newRule;
		}

		private boolean shouldBeAnnotated(Atom a, int ruleStratum, boolean wouldBeDelta) {
			// XXX Do we want to also exclude aggregates? I don't think so.
			Symbol sym = a.getSymbol();
			return !a.isNegated() && sym.getSymbolType().isIDBSymbol()
					&& (wouldBeDelta || getStratumRank(sym) == ruleStratum);
		}

		private Rule sort(Rule r) {
			List<Atom> newBody = new ArrayList<>(Util.iterableToList(r.getBody()));
			sort(newBody);
			return BasicRule.get(r.getHead(), newBody);
		}

		private void sort(List<Atom> body) {
			try {
				Set<Var> boundVars = new HashSet<>();
				for (int i = 0; i < body.size(); ++i) {
					for (int j = i; j < body.size(); ++j) {
						if (Unification.canBindVars(body.get(j), boundVars)) {
							boundVars.addAll(Atoms.varSet(body.get(j)));
							Collections.swap(body, i, j);
							break;
						}
					}
				}
			} catch (InvalidProgramException e) {
				throw new AssertionError();
			}
		}

	}

}
