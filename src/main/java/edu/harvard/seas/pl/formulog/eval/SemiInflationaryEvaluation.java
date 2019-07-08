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
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer.InputSymbol;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer.SupSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbolFactory.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;
import edu.harvard.seas.pl.formulog.validating.Validator;

public class SemiInflationaryEvaluation implements Evaluation {

	private final ValidProgram prog;
	private final Map<Integer, Set<IndexedRule>> safeRules = new HashMap<>();
	private final Map<Integer, Set<IndexedRule>> delayedRules = new HashMap<>();
	private final Map<Integer, Set<IndexedRule>> safeFirstRoundRules = new HashMap<>();
	private final Map<Integer, Set<IndexedRule>> unsafeFirstRoundRules = new HashMap<>();
	private final IndexedFactDBBuilder dbb;
	private IndexedFactDB cumulativeDb;
	private final Map<Integer, IndexedFactDB> generationalDbs = new HashMap<>();
	private Map<Integer, IndexedFactDB> deltaOldSafe = new HashMap<>();
	private Map<Integer, IndexedFactDB> deltaNewSafe = new HashMap<>();
	private Map<Integer, IndexedFactDB> deltaOldUnsafe = new HashMap<>();
	private Map<Integer, IndexedFactDB> deltaNewUnsafe = new HashMap<>();
	private Map<NormalAtom, Integer> deltaOldGenerations = new HashMap<>();
	private int botStratum = Integer.MAX_VALUE;
	private int topStratum = 0;
	private Map<Symbol, Set<Integer>> relevantStrata = new HashMap<>();
	private Set<Integer> safeFirstRoundsCompleted = new HashSet<>();
	private Set<Integer> unsafeFirstRoundsCompleted = new HashSet<>();

	public static SemiInflationaryEvaluation setup(WellTypedProgram prog, boolean useDemandTransformation)
			throws InvalidProgramException {
		Program reorderedProg = reorder(prog);
		Program magicProg = (new MagicSetTransformer(reorderedProg)).transform(useDemandTransformation, false);
		ValidProgram vprog = (new Validator(magicProg)).validate();
		return new SemiInflationaryEvaluation(vprog);
	}

	private SemiInflationaryEvaluation(ValidProgram prog) {
		this.prog = prog;
		this.dbb = new IndexedFactDBBuilder(prog);
	}

	public ValidProgram getProgram() {
		return prog;
	}

	public synchronized void run(int parallelism) throws EvaluationException {
		run();
	}

	public synchronized void run() throws EvaluationException {
		if (cumulativeDb == null) {
			preprocessRules();
			cumulativeDb = dbb.build();
			for (Symbol sym : prog.getFactSymbols()) {
				for (Atom fact : prog.getFacts(sym)) {
					cumulativeDb.add((NormalAtom) fact);
				}
			}
			for (Map.Entry<Integer, Set<IndexedRule>> e : safeFirstRoundRules.entrySet()) {
				if (e.getValue().isEmpty()) {
					continue;
				}
				System.out.println("\nSAFE FIRST ROUND RULES FOR #" + e.getKey());
				for (IndexedRule r : e.getValue()) {
					System.out.println(r);
				}
			}
			for (Map.Entry<Integer, Set<IndexedRule>> e : safeRules.entrySet()) {
				if (e.getValue().isEmpty()) {
					continue;
				}
				System.out.println("\nSAFE RULES FOR #" + e.getKey());
				for (IndexedRule r : e.getValue()) {
					System.out.println(r);
				}
			}
			for (Map.Entry<Integer, Set<IndexedRule>> e : unsafeFirstRoundRules.entrySet()) {
				if (e.getValue().isEmpty()) {
					continue;
				}
				System.out.println("\nUNSAFE FIRST ROUND RULES FOR #" + e.getKey());
				for (IndexedRule r : e.getValue()) {
					System.out.println(r);
				}
			}
			for (Map.Entry<Integer, Set<IndexedRule>> e : delayedRules.entrySet()) {
				if (e.getValue().isEmpty()) {
					continue;
				}
				System.out.println("\nUNSAFE RULES FOR #" + e.getKey());
				for (IndexedRule r : e.getValue()) {
					System.out.println(r);
				}
			}
			System.out.println("\nRELEVANT STRATA " + relevantStrata);
			evaluate();
		}
	}

	public synchronized IndexedFactDB getResult() {
		if (cumulativeDb == null) {
			throw new IllegalStateException("Must run evaluation before requesting result.");
		}
		return cumulativeDb;
	}

	private void evaluate() throws EvaluationException {
		boolean changed = true;
		outer: while (true) {
			while (changed) {
				changed = false;
				for (int stratum = botStratum; stratum <= topStratum; ++stratum) {
					changed |= evaluateStratum(stratum, true);
				}
			}
			for (int stratum = botStratum; stratum <= topStratum; ++stratum) {
				changed |= evaluateStratum(stratum, false);
				if (changed) {
					continue outer;
				}
			}
			break;
		}
	}

	private boolean evaluateStratum(int stratum, boolean safe) throws EvaluationException {
		System.out.println("\n**********\nEVALUATING STRATUM " + stratum + " (safe=" + safe + ")");
		boolean changed = false;
		Set<Integer> s = safe ? safeFirstRoundsCompleted : unsafeFirstRoundsCompleted;
		Map<Integer, IndexedFactDB> deltaOld = safe ? deltaOldSafe : deltaOldUnsafe;
		Map<Integer, IndexedFactDB> deltaNew = safe ? deltaNewSafe : deltaNewUnsafe;
		if (s.add(stratum)) {
			deltaOld.put(stratum, deltaNew.get(stratum));
			Map<Integer, Set<IndexedRule>> m = safe ? safeFirstRoundRules : unsafeFirstRoundRules;
			Set<IndexedRule> rs = m.get(stratum);
			if (rs != null) {
				for (IndexedRule r : rs) {
					changed |= (new RuleEvaluator(r, deltaOld.get(stratum))).evaluate();
				}
			}
		}
		if (!deltaOld.containsKey(stratum)) {
			return changed;
		}
		boolean changedLastRound = true;
		while (changedLastRound) {
			changedLastRound = false;
			deltaOld.put(stratum, deltaNew.get(stratum));
			deltaNew.put(stratum, dbb.build());
			Map<Integer, Set<IndexedRule>> m = safe ? safeRules : delayedRules;
			Set<IndexedRule> rs = m.get(stratum);
			if (rs != null) {
				for (IndexedRule r : rs) {
					changedLastRound |= (new RuleEvaluator(r, deltaOld.get(stratum))).evaluate();
				}
			}
			changed |= changedLastRound;
		}
		System.out.println("**********");
		return changed;
	}

	private static enum Gen {
		DELTA_GEN, ZERO_GEN, ALL_GEN;
	}

	private class RuleEvaluator {

		private final IndexedRule r;
		private final IndexedFactDB deltaDb;
		private final RuleSubstitution s;
		// private final int deltaStratum;
		private final boolean empty;
		private final int headStratum;

		public RuleEvaluator(IndexedRule r, IndexedFactDB deltaDb) {
			this.r = r;
			this.deltaDb = deltaDb;
			s = new RuleSubstitution(r);
			Symbol fst = r.getBody(0).getSymbol();
			// int deltaStratum = -1;
			boolean empty = false;
			if (fst instanceof SemiNaiveSymbol) {
				// SemiNaiveSymbol sym = (SemiNaiveSymbol) fst;
				// assert sym.getSemiNaiveSymbolType().equals(SemiNaiveSymbolType.DELTA);
				// deltaStratum = getStratumRank(sym);
				if (!deltaDb.query(stripSemiNaiveAnnotation(fst)).iterator().hasNext()) {
					empty = true;
				}
			}
			this.empty = empty;
			this.headStratum = getStratumRank(r.getHead().getSymbol());
			// System.out.println("DELTA\n" + deltaDb);
		}

		private Gen getGenToUse(Symbol sym) {
			int stratum = getStratumRank(stripSemiNaiveAnnotation(sym));
			if (stratum == headStratum) {
				return Gen.DELTA_GEN;
			} else if (stratum < headStratum) {
				return Gen.ALL_GEN;
			} else {
				return Gen.ZERO_GEN;
			}
			// if (stratum >= deltaStratum) {
			// return Gen.DELTA_GEN;
			// } else {
			// return Gen.ALL_GEN;
			// }
		}

		public boolean evaluate() throws EvaluationException {
			if (empty) {
				return false;
			}
			System.out.println("\n" + r);
			return evaluate(0, -1);
		}

		private boolean evaluate(int pos, int runningGen) throws EvaluationException {
			if (pos >= r.getBodySize()) {
				NormalAtom hd = (NormalAtom) r.getHead();
				Symbol hdSym = hd.getSymbol();
				int gen = -1;
				switch (getGenToUse(hdSym)) {
				case ALL_GEN:
					throw new AssertionError("impossible");
				case DELTA_GEN:
					gen = runningGen;
					break;
				case ZERO_GEN:
					gen = 0;
					break;
				}
				if (gen < 0) {
					gen = 0;
				}
				if (incrementGen(hdSym)) {
					gen++;
				}
				return reportFact(hd, s, gen);
			}
			s.setToBefore(pos);
			return r.getBody(pos).visit(new AtomVisitorExn<Void, Boolean, EvaluationException>() {

				@Override
				public Boolean visit(NormalAtom normalAtom, Void in) throws EvaluationException {
					Symbol sym = normalAtom.getSymbol();
					Iterable<NormalAtom> facts;
					int dbIdx = r.getDBIndex(pos);
					if (sym.getSymbolType().isIDBSymbol() && normalAtom.isNegated()) {
						facts = getFacts(sym, dbIdx, runningGen);
					} else if (sym instanceof SemiNaiveSymbol) {
						SemiNaiveSymbol snSym = (SemiNaiveSymbol) sym;
						switch (snSym.getSemiNaiveSymbolType()) {
						case CURRENT:
							if (runningGen < 0) {
								return go(normalAtom, dbIdx, false);
							}
							facts = getFacts(sym, dbIdx, runningGen);
							break;
						case DELTA:
							assert pos == 0;
							return handleDelta(normalAtom, false);
						case DELTA_LOWER:
							assert pos == 0;
							return handleDelta(normalAtom, true);
						case PREVIOUS:
							if (runningGen < 0) {
								return go(normalAtom, dbIdx, true);
							}
							facts = getFacts(sym, dbIdx, runningGen - 1);
							break;
						default:
							throw new AssertionError("impossible");
						}
					} else {
						facts = getAll(dbIdx, s);
					}
					return handleAtom(normalAtom, facts, runningGen);
				}

				private boolean go(NormalAtom atom, int dbIdx, boolean isPrevious) throws EvaluationException {
					atom = (NormalAtom) Atoms.get(stripSemiNaiveAnnotation(atom.getSymbol()), atom.getArgs(), atom.isNegated());
					boolean changed = false;
					for (NormalAtom fact : getAll(dbIdx, s)) {
						int gen = deltaOldGenerations.get(fact);
						s.setToBefore(pos);
						if (Unification.unify(atom, fact, s)) {
							System.out.println("matched on " + fact + " at gen " + gen);
							changed |= evaluate(pos + 1, isPrevious ? gen + 1 : gen);
						}
					}
					return changed;
				}

				private Iterable<NormalAtom> getFacts(Symbol sym, int dbIdx, int deltaRelativeGen)
						throws EvaluationException {
					switch (getGenToUse(sym)) {
					case ALL_GEN:
						System.out.println("Looking up all for " + sym);
						return getAll(dbIdx, s);
					case DELTA_GEN:
						System.out.println("Looking up " + sym + " at gen " + deltaRelativeGen);
						return get(dbIdx, s, deltaRelativeGen);
					case ZERO_GEN:
						System.out.println("Looking up " + sym + " at gen 0");
						return get(dbIdx, s, 0);
					}
					throw new AssertionError("impossible");
				}

				private boolean handleDelta(NormalAtom a, boolean ignoreGen) throws EvaluationException {
					Symbol sym = stripSemiNaiveAnnotation(a.getSymbol());
					// IndexedFactDB db = delta.get(sym);
					// if (db == null) {
					// System.out.println("db null");
					// return false;
					// }
					Iterator<NormalAtom> it = deltaDb.query(sym).iterator();
					if (!it.hasNext()) {
						return false;
					}
					a = (NormalAtom) Atoms.get(sym, a.getArgs(), a.isNegated());
					boolean changed = false;
					while (it.hasNext()) {
						NormalAtom fact = it.next();
						int genToUse = ignoreGen ? runningGen : deltaOldGenerations.get(fact);
						s.setToBefore(pos);
						if (Unification.unify(a, fact, s)) {
							System.out.println("matched " + fact + " at gen " + genToUse);
							changed |= evaluate(pos + 1, genToUse);
						}
					}
					return changed;
				}

				private boolean handleAtom(NormalAtom a, Iterable<NormalAtom> facts, int deltaGen)
						throws EvaluationException {
					Iterator<NormalAtom> it = facts.iterator();
					if (a.isNegated()) {
						return !it.hasNext() && evaluate(pos + 1, deltaGen);
					} else {
						boolean changed = false;
						while (it.hasNext()) {
							s.setToBefore(pos);
							NormalAtom fact = it.next();
							// System.out.println(cumulativeDb);
							// System.out.println("a " + a);
							// System.out.println("fact " + fact);
							Unification.unsafeUnifyWithFact(a, fact, s);
							changed |= evaluate(pos + 1, deltaGen);
						}
						return changed;
					}
				}

				@Override
				public Boolean visit(UnifyAtom unifyAtom, Void in) throws EvaluationException {
					Term[] args = unifyAtom.getArgs();
					if (unifyAtom.isNegated() ^ Unification.unify(args[0], args[1], s)) {
						return evaluate(pos + 1, runningGen);
					}
					return false;
				}

			}, null);
		}

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
		System.out.print("Discovered fact " + fact + " at generation " + gen + "...");
		boolean isAgg = prog.getRelationProperties(sym).isAggregated();
		if (isAgg && (fact = checkAggregateFact(fact, gen)) != null || !isAgg && checkNonAggregateFact(fact, gen)) {
			System.out.println(" added");
			for (Integer stratum : Util.lookupOrCreate(relevantStrata, sym, () -> Collections.emptySet())) {
				// Map<Symbol, IndexedFactDB> m = Util.lookupOrCreate(deltaNewSafe, stratum, ()
				// -> new HashMap<>());
				// IndexedFactDB db = Util.lookupOrCreate(m, sym, () -> dbb.build());
				// db.add(fact);
				// m = Util.lookupOrCreate(deltaNewUnsafe, stratum, () -> new HashMap<>());
				// db = Util.lookupOrCreate(m, sym, () -> dbb.build());
				// db.add(fact);
				Util.lookupOrCreate(deltaNewSafe, stratum, () -> dbb.build()).add(fact);
				Util.lookupOrCreate(deltaNewUnsafe, stratum, () -> dbb.build()).add(fact);
			}
			assert !deltaOldGenerations.containsKey(fact);
			deltaOldGenerations.put(fact, gen);
			Util.lookupOrCreate(generationalDbs, gen, () -> dbb.build()).add(fact);
			cumulativeDb.add(fact);
			// System.out.println("added");
			return true;
		} else {
			System.out.println(" not added");
			return false;
		}
	}

	private Symbol stripSemiNaiveAnnotation(Symbol sym) {
		if (sym instanceof SemiNaiveSymbol) {
			return ((SemiNaiveSymbol) sym).getUnderlyingSymbol();
		}
		return sym;
	}

	private static boolean incrementGen(Symbol sym) {
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

	private NormalAtom checkAggregateFact(NormalAtom fact, int gen) throws EvaluationException {
		Symbol sym = fact.getSymbol();
		Term aggValue = fact.getArgs()[sym.getArity() - 1];
		Symbol funcSym = prog.getRelationProperties(sym).getAggFuncSymbol();
		FunctionDef aggFunc = prog.getDef(funcSym);
		for (int i = gen; i >= 0; --i) {
			IndexedFactDB db = Util.lookupOrCreate(generationalDbs, i, () -> dbb.build());
			Term oldAgg = db.getClosestAggregateValue(fact);
			if (oldAgg != null) {
				Term newAgg = aggFunc.evaluate(new Term[] { aggValue, oldAgg });
				if (!newAgg.equals(oldAgg)) {
					Term[] args = fact.getArgs();
					Term[] newArgs = new Term[args.length];
					System.arraycopy(args, 0, newArgs, 0, args.length - 1);
					newArgs[args.length - 1] = newAgg;
					return (NormalAtom) Atoms.getPositive(sym, newArgs);
				}
				return null;
			}
		}
		return fact;
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
			boolean firstRoundRule = isFirstRoundRule(original);
			recordStratum(stratum);
			for (Rule semiNaiveRule : makeSemiNaiveRules(original, stratum)) {
				IndexedRule indexedRule = new IndexedRule(semiNaiveRule, dbb);
				Map<Integer, Set<IndexedRule>> m;
				if (safe && firstRoundRule) {
					m = safeFirstRoundRules;
				} else if (safe) {
					m = safeRules;
				} else if (firstRoundRule) {
					m = unsafeFirstRoundRules;
				} else {
					m = delayedRules;
				}
				m.get(stratum).add(indexedRule);
			}
		}

		private void recordStratum(int stratum) {
			safeRules.putIfAbsent(stratum, new HashSet<>());
			delayedRules.putIfAbsent(stratum, new HashSet<>());
			safeFirstRoundRules.putIfAbsent(stratum, new HashSet<>());
			unsafeFirstRoundRules.putIfAbsent(stratum, new HashSet<>());
			deltaOldSafe.putIfAbsent(stratum, dbb.build());
			deltaNewSafe.putIfAbsent(stratum, dbb.build());
			deltaOldUnsafe.putIfAbsent(stratum, dbb.build());
			deltaNewUnsafe.putIfAbsent(stratum, dbb.build());
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

		private boolean isFirstRoundRule(Rule r) {
			for (Atom a : r.getBody()) {
				Symbol sym = a.getSymbol();
				if (sym.getSymbolType().isIDBSymbol()) {
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
					Symbol sym = normalAtom.getSymbol();
					boolean notOk = normalAtom.isNegated() && sym.getSymbolType().isIDBSymbol();
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
							boolean safe = true;
							if (sym instanceof PredicateFunctionSymbol) {
								DummyFunctionDef dummy = (DummyFunctionDef) def;
								setPredicateFunction(dummy);
								safe = false;
							} else if (def instanceof CustomFunctionDef) {
								safe = preprocess(((CustomFunctionDef) def).getBody());
							}
							for (Term t : funcCall.getArgs()) {
								safe &= preprocess(t);
							}
							return safe;
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

		private Set<Rule> makeSemiNaiveRules(Rule original, int stratum) {
			Set<Rule> rules = new HashSet<>();
			int i = 0;
			for (Atom a : original.getBody()) {
				if (shouldBeAnnotated(a, stratum, true)) {
					Util.lookupOrCreate(relevantStrata, a.getSymbol(), () -> new HashSet<>()).add(stratum);
					rules.add(makeSemiNaiveRule(original, i, stratum));
				}
				i++;
			}
			if (rules.isEmpty()) {
				return Collections.singleton(sort(original));
			}
			return rules;
		}

		private Rule makeSemiNaiveRule(Rule original, int deltaPos, int stratum) {
			List<Atom> newBody = new ArrayList<>();
			int i = 0;
			for (Atom a : original.getBody()) {
				if (shouldBeAnnotated(a, stratum, i == deltaPos)) {
					SemiNaiveSymbolType type;
					if (i < deltaPos) {
						type = SemiNaiveSymbolType.CURRENT;
					} else if (i > deltaPos) {
						// type = SemiNaiveSymbolType.PREVIOUS;
						type = SemiNaiveSymbolType.CURRENT;
					} else if (getStratumRank(a.getSymbol()) == stratum) {
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

		private boolean shouldBeAnnotated(Atom a, int stratum, boolean wouldBeDelta) {
			// XXX Do we want to also exclude aggregates? I don't think so.
			Symbol sym = a.getSymbol();
			return !a.isNegated() && sym.getSymbolType().isIDBSymbol()
					&& (wouldBeDelta || getStratumRank(sym) == stratum);
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
	
	private static Program reorder(Program prog) {
		Map<Symbol, Set<Rule>> newRules = new HashMap<>();
		for (Symbol sym : prog.getRuleSymbols()) {
			Set<Rule> s = new HashSet<>();
			for (Rule r : prog.getRules(sym)) {
				s.add(reorder(r));
			}
			newRules.put(sym, s);
		}
		return new Program() {

			@Override
			public Set<Symbol> getFunctionSymbols() {
				return prog.getFunctionSymbols();
			}

			@Override
			public Set<Symbol> getFactSymbols() {
				return prog.getFactSymbols();
			}

			@Override
			public Set<Symbol> getRuleSymbols() {
				return prog.getRuleSymbols();
			}

			@Override
			public FunctionDef getDef(Symbol sym) {
				return prog.getDef(sym);
			}

			@Override
			public Set<Atom> getFacts(Symbol sym) {
				return prog.getFacts(sym);
			}

			@Override
			public Set<Rule> getRules(Symbol sym) {
				return newRules.get(sym);
			}

			@Override
			public SymbolManager getSymbolManager() {
				return prog.getSymbolManager();
			}

			@Override
			public RelationProperties getRelationProperties(Symbol sym) {
				return prog.getRelationProperties(sym);
			}

			@Override
			public boolean hasQuery() {
				return prog.hasQuery();
			}

			@Override
			public NormalAtom getQuery() {
				return prog.getQuery();
			}
			
		};
	}
	
	private static Rule reorder(Rule r) {
		List<Atom> newBody = new ArrayList<>();
		for (Atom a : r.getBody()) {
			if (!a.isNegated()) {
				newBody.add(a);
			}
		}
		for (Atom a : r.getBody()) {
			if (a.isNegated()) {
				newBody.add(a);
			}
		}
		return BasicRule.get(r.getHead(), newBody);
	}

}
