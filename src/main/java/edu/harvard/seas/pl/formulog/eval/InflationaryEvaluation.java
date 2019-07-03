package edu.harvard.seas.pl.formulog.eval;

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
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB.IndexedFactDBBuilder;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbolFactory.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class InflationaryEvaluation {

	private final Program prog;
	private final Set<IndexedRule> safeRules = new HashSet<>();
	private final Map<Integer, Set<IndexedRule>> delayedRules = new HashMap<>();
	private final IndexedFactDBBuilder dbb;
	private IndexedFactDB cumulativeDb;
	private final Map<Integer, IndexedFactDB> generationalDbs = new HashMap<>();
	private final Map<Symbol, Map<Integer, Set<Atom>>> delta = new HashMap<>();

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
		evaluate();
		// System.out.println("SAFE");
		// for (Map.Entry<Integer, Set<IndexedRule>> e : safeRules.entrySet()) {
		// System.out.println(e.getKey());
		// for (IndexedRule r : e.getValue()) {
		// System.out.println(r);
		// }
		// }
		// System.out.println("DELAYED");
		// for (Map.Entry<Integer, Set<IndexedRule>> e : delayedRules.entrySet()) {
		// System.out.println(e.getKey());
		// for (IndexedRule r : e.getValue()) {
		// System.out.println(r);
		// }
		// }
		return cumulativeDb;
	}

	private void evaluate() throws EvaluationException {
		for (IndexedRule r : safeRules) {
			evaluate(r, 0, new RuleSubstitution(r), 0);
		}
	}

	private void evaluate(IndexedRule r, int i, RuleSubstitution s, int gen) throws EvaluationException {
		if (i >= r.getBodySize()) {
			reportFact((NormalAtom) r.getHead(), s, gen);
			return;
		}
		s.setToBefore(i);
		r.getBody(i).visit(new AtomVisitorExn<Void, Void, EvaluationException>() {

			@Override
			public Void visit(NormalAtom normalAtom, Void in) throws EvaluationException {
				Symbol sym = normalAtom.getSymbol();
				Iterable<NormalAtom> facts;
				int dbIdx = r.getDBIndex(i);
				if (sym instanceof SemiNaiveSymbol) {
					SemiNaiveSymbol snSym = (SemiNaiveSymbol) sym;
					switch (snSym.getSemiNaiveSymbolType()) {
					case CURRENT:
						facts = get(dbIdx, s, gen);
						break;
					case DELTA:
						handleDelta(normalAtom);
						return null;
					case PREVIOUS:
						facts = get(dbIdx, s, gen - 1);
						break;
					default:
						throw new AssertionError("impossible");
					}
				} else {
					facts = getAll(dbIdx, s);
				}
				handleAtom(normalAtom, facts, gen);
				return null;
			}
			
			private void handleDelta(NormalAtom a) {
				
			}
			
			private void handleAtom(NormalAtom a, Iterable<NormalAtom> facts, int gen) {
				
			}

			@Override
			public Void visit(UnifyAtom unifyAtom, Void in) throws EvaluationException {
				Term[] args = unifyAtom.getArgs();
				if (unifyAtom.isNegated() ^ Unification.unify(args[0], args[1], s)) {
					evaluate(r, i + 1, s, gen);
				}
				return null;
			}

		}, null);
	}

	private int getStratumRank(Symbol sym) {
		if (sym.getSymbolType().isEDBSymbol()) {
			return -1;
		}
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
						if (pos > its.size()) {
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

	private void reportFact(NormalAtom atom, Substitution s, int gen) throws EvaluationException {
		NormalAtom fact = (NormalAtom) Atoms.normalize(atom, s);
		System.out.println(fact);
		// XXX do something
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
			for (Rule semiNaiveRule : makeSemiNaiveRules(original, stratum)) {
				IndexedRule indexedRule = new IndexedRule(semiNaiveRule, dbb);
				if (safe) {
					safeRules.add(indexedRule);
				} else {
					Util.lookupOrCreate(delayedRules, stratum, () -> new HashSet<>()).add(indexedRule);
				}
			}
		}

		private boolean allVars(Term[] ts) {
			for (Term t : ts) {
				if (!(t instanceof Var)) {
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
								// TODO Try to set it, and return false
								throw new UnsupportedOperationException();
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

		private Set<Rule> makeSemiNaiveRules(Rule original, int stratum) {
			Set<Rule> rules = new HashSet<>();
			int i = 0;
			for (Atom a : original.getBody()) {
				if (shouldBeAnnotated(a, stratum)) {
					rules.add(makeSemiNaiveRule(original, i, stratum));
				}
				i++;
			}
			if (rules.isEmpty()) {
				return Collections.singleton(original);
			}
			return rules;
		}

		private Rule makeSemiNaiveRule(Rule original, int deltaPos, int stratum) {
			List<Atom> newBody = new ArrayList<>();
			int i = 0;
			for (Atom a : original.getBody()) {
				if (shouldBeAnnotated(a, stratum)) {
					SemiNaiveSymbolType type;
					if (i < deltaPos) {
						type = SemiNaiveSymbolType.CURRENT;
					} else if (i > deltaPos) {
						type = SemiNaiveSymbolType.PREVIOUS;
					} else {
						type = SemiNaiveSymbolType.DELTA;
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

		private boolean shouldBeAnnotated(Atom a, int ruleStratum) {
			// XXX Do we want to also exclude aggregates? I don't think so.
			Symbol sym = a.getSymbol();
			return !a.isNegated() && sym.getSymbolType().isIDBSymbol() && getStratumRank(sym) == ruleStratum;
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
