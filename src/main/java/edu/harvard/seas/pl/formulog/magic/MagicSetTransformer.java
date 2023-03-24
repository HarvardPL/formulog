package edu.harvard.seas.pl.formulog.magic;

/*-
 * #%L
 * Formulog
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
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.AbstractWrappedRelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.util.DedupWorkList;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;

public class MagicSetTransformer {

	private final Program<UserPredicate, BasicRule> origProg;
	private boolean topDownIsDefault;

	private static final boolean debug = Configuration.debugMst;

	public MagicSetTransformer(Program<UserPredicate, BasicRule> prog) {
		this.origProg = prog;
	}

	public BasicProgram transform(boolean useDemandTransformation, boolean restoreStratification)
			throws InvalidProgramException {
		BasicProgram prog;
		if (origProg.hasQuery()) {
			prog = transformForQuery(origProg.getQuery(), useDemandTransformation, restoreStratification);
		} else {
			prog = transformNoQuery(useDemandTransformation, restoreStratification);
		}
		if (debug) {
			System.err.println("Rewritten rules...");
			List<RelationSymbol> syms = prog.getRuleSymbols().stream().sorted(SymbolComparator.INSTANCE)
					.collect(Collectors.toList());
			for (RelationSymbol sym : syms) {
				for (BasicRule r : prog.getRules(sym)) {
					System.err.println(r);
				}
			}
		}
		return prog;
	}

	private BasicProgram transformForQuery(UserPredicate query, boolean useDemandTransformation,
			boolean restoreStratification) throws InvalidProgramException {
		topDownIsDefault = true;
		if (query.isNegated()) {
			throw new InvalidProgramException("Query cannot be negated");
		}
		BasicProgram newProg;
		if (query.getSymbol().isEdbSymbol()) {
			newProg = makeEdbProgram(query);
		} else {
			UserPredicate adornedQuery = Adornments.adorn(query, Collections.emptySet(), topDownIsDefault);
			Set<Pair<BasicRule, Integer>> adRules = adorn(Collections.singleton(adornedQuery.getSymbol()));
			Set<BasicRule> magicRules = makeMagicRules(adRules);
			magicRules.add(makeSeedRule(adornedQuery));
			BasicRule queryRule = makeQueryRule(adornedQuery);
			UserPredicate newQuery = queryRule.getHead();
			BasicProgram magicProg = new ProgramImpl(magicRules, newQuery);
			if (restoreStratification && !isStratified(magicProg)) {
				magicProg = stratify(magicProg, Pair.map(adRules, (rule, num) -> rule));
			}
			((ProgramImpl) magicProg).rules.put(newQuery.getSymbol(), Collections.singleton(queryRule));
			if (useDemandTransformation) {
				magicProg = applyDemandTransformation(magicProg, restoreStratification);
			}
			newProg = magicProg;
		}
		return newProg;
	}

	private BasicRule makeSeedRule(UserPredicate adornedQuery) {
		return BasicRule.make(createInputAtom(adornedQuery));
	}

	private BasicRule makeQueryRule(UserPredicate query) {
		RelationSymbol oldSym = query.getSymbol();
		RelationSymbol querySym = new RelationSymbol() {

			@Override
			public FunctorType getCompileTimeType() {
				return oldSym.getCompileTimeType();
			}

			@Override
			public int getArity() {
				return oldSym.getArity();
			}

			@Override
			public boolean isIdbSymbol() {
				return true;
			}

			@Override
			public boolean isBottomUp() {
				return true;
			}

			@Override
			public boolean isTopDown() {
				return false;
			}

			@Override
			public boolean isDisk() {
				return false;
			}

			@Override
			public String toString() {
				Symbol sym = oldSym;
				if (oldSym instanceof AdornedSymbol) {
					sym = ((AdornedSymbol) oldSym).getBaseSymbol();
				}
				return "query:" + sym;
			}

		};
		Term[] args = query.getArgs();
		Term[] newArgs = new Term[args.length];
		Term[] hdArgs = new Term[args.length];
		List<ComplexLiteral> body = new ArrayList<>();
		Set<Var> seen = new HashSet<>();
		for (int i = 0; i < args.length; ++i) {
			Term t = args[i];
			if (!(t instanceof Var) || !seen.add((Var) t)) {
				Var x = Var.fresh();
				body.add(UnificationPredicate.make(x, t, false));
				t = x;
			}
			newArgs[i] = hdArgs[i] = t;
		}
		body.add(0, UserPredicate.make(oldSym, newArgs, query.isNegated()));
		UserPredicate hd = UserPredicate.make(querySym, hdArgs, query.isNegated());
		return BasicRule.make(hd, body);
	}

	private BasicProgram makeEdbProgram(UserPredicate query) {
		BasicRule queryRule = makeQueryRule(query);
		RelationSymbol oldQuerySym = query.getSymbol();
		return new BasicProgram() {

			@Override
			public Set<FunctionSymbol> getFunctionSymbols() {
				return Collections.emptySet();
			}

			@Override
			public Set<RelationSymbol> getFactSymbols() {
				return Collections.singleton(oldQuerySym);
			}

			@Override
			public Set<RelationSymbol> getRuleSymbols() {
				return Collections.singleton(getQuery().getSymbol());
			}

			@Override
			public FunctionDef getDef(FunctionSymbol sym) {
				throw new IllegalArgumentException("No definition for function with symbol: " + sym);
			}

			@Override
			public Set<Term[]> getFacts(RelationSymbol sym) {
				if (oldQuerySym.equals(sym)) {
					return origProg.getFacts(oldQuerySym);
				}
				return Collections.emptySet();
			}

			@Override
			public Set<BasicRule> getRules(RelationSymbol sym) {
				if (!sym.equals(getQuery().getSymbol())) {
					return Collections.emptySet();
				}
				return Collections.singleton(queryRule);
			}

			@Override
			public SymbolManager getSymbolManager() {
				return origProg.getSymbolManager();
			}

			@Override
			public boolean hasQuery() {
				return true;
			}

			@Override
			public UserPredicate getQuery() {
				return queryRule.getHead();
			}

			@Override
			public FunctionCallFactory getFunctionCallFactory() {
				return origProg.getFunctionCallFactory();
			}

			@Override
			public Set<ConstructorSymbol> getUninterpretedFunctionSymbols() {
				return origProg.getUninterpretedFunctionSymbols();
			}

			@Override
			public Set<TypeSymbol> getTypeSymbols() {
				return origProg.getTypeSymbols();
			}

		};
	}

	private BasicProgram transformNoQuery(boolean useDemandTransformation, boolean restoreStratification)
			throws InvalidProgramException {
		topDownIsDefault = false;
		Set<RelationSymbol> bottomUpSymbols = new HashSet<>();
		for (RelationSymbol sym : origProg.getRuleSymbols()) {
			if (!sym.isTopDown()) {
				bottomUpSymbols.add(sym);
			}
		}
		Set<Pair<BasicRule, Integer>> adRules = adorn(bottomUpSymbols);
		Set<BasicRule> magicRules = makeMagicRules(adRules);
		BasicProgram magicProg = new ProgramImpl(magicRules, null);
		if (restoreStratification && !isStratified(magicProg)) {
			magicProg = stratify(magicProg, Pair.map(adRules, (rule, num) -> rule));
		}
		if (useDemandTransformation) {
			magicProg = applyDemandTransformation(magicProg, restoreStratification);
		}
		return magicProg;
	}

	private BasicProgram applyDemandTransformation(BasicProgram prog, boolean mustBeStratified)
			throws InvalidProgramException {
		BasicProgram prog2 = stripAdornments(prog);
		if (isStratified(prog2)) {
			return prog2;
		}
		return prog;
	}

	private BasicProgram stripAdornments(BasicProgram prog) throws InvalidProgramException {
		Set<BasicRule> rules = new HashSet<>();
		for (RelationSymbol sym : prog.getRuleSymbols()) {
			for (BasicRule r : prog.getRules(sym)) {
				UserPredicate newHead = stripAdornment(r.getHead());
				List<ComplexLiteral> newBody = new ArrayList<>();
				for (ComplexLiteral atom : r) {
					newBody.add(stripAdornment(atom));
				}
				rules.add(BasicRule.make(newHead, newBody));
			}
		}
		UserPredicate query = null;
		if (prog.hasQuery()) {
			query = stripAdornment(prog.getQuery());
		}
		return new ProgramImpl(rules, query);
	}

	private static <C extends ComplexLiteral> C stripAdornment(C atom) {
		return atom.accept(new ComplexLiteralVisitor<Void, C>() {

			@SuppressWarnings("unchecked")
			@Override
			public C visit(UnificationPredicate unificationPredicate, Void input) {
				return (C) unificationPredicate;
			}

			@SuppressWarnings("unchecked")
			@Override
			public C visit(UserPredicate userPredicate, Void input) {
				RelationSymbol sym = userPredicate.getSymbol();
				if (sym instanceof PositiveSymbol) {
					sym = ((PositiveSymbol) sym).getBaseSymbol();
					if (sym instanceof AdornedSymbol) {
						sym = ((AdornedSymbol) sym).getBaseSymbol();
					}
					sym = new PositiveSymbol(sym);
				} else if (sym instanceof AdornedSymbol) {
					sym = ((AdornedSymbol) sym).getBaseSymbol();
				}
				return (C) UserPredicate.make(sym, userPredicate.getArgs(), userPredicate.isNegated());
			}

		}, null);
	}

	private Set<Pair<BasicRule, Integer>> adorn(Set<RelationSymbol> seeds) throws InvalidProgramException {
		if (debug) {
			System.err.println("Adorning rules...");
		}
		Set<Pair<BasicRule, Integer>> adRules = new HashSet<>();
		DedupWorkList<RelationSymbol> worklist = new DedupWorkList<>();
		for (RelationSymbol seed : seeds) {
			worklist.push(seed);
		}
		HiddenPredicateFinder hpf = new HiddenPredicateFinder(origProg);
		int ruleNum = 0;
		while (!worklist.isEmpty()) {
			RelationSymbol adSym = worklist.pop();
			RelationSymbol origSym = adSym;
			if (adSym instanceof AdornedSymbol) {
				origSym = ((AdornedSymbol) adSym).getBaseSymbol();
			}
			for (BasicRule r : origProg.getRules(origSym)) {
				for (RelationSymbol sym : hpf.visit(r)) {
					if (exploreTopDown(sym)) {
						throw new InvalidProgramException("Cannot refer to top-down IDB predicate " + sym
								+ " in a function; consider annotating " + sym + " with @bottomup");
					}
					if (sym.isIdbSymbol()) {
						worklist.push(sym);
					}
				}
				UserPredicate head = r.getHead();
				UserPredicate adHead = UserPredicate.make(adSym, head.getArgs(), head.isNegated());
				BasicRule adRule = Adornments.adornRule(adHead, Util.iterableToList(r), topDownIsDefault);
				for (ComplexLiteral a : adRule) {
					a.accept(new ComplexLiteralVisitor<Void, Void>() {

						@Override
						public Void visit(UnificationPredicate unificationPredicate, Void input) {
							// Do nothing
							return null;
						}

						@Override
						public Void visit(UserPredicate userPredicate, Void input) {
							RelationSymbol sym = userPredicate.getSymbol();
							if (sym.isIdbSymbol()) {
								worklist.push(sym);
							}
							return null;
						}

					}, null);
				}
				if (debug) {
					System.err.println("--" + ruleNum + "--\n" + adRule);
				}
				adRules.add(new Pair<>(adRule, ruleNum));
				ruleNum++;
			}
		}
		return adRules;
	}

	private Set<BasicRule> makeMagicRules(Set<Pair<BasicRule, Integer>> adornedRules) {
		Set<BasicRule> magicRules = new HashSet<>();
		for (Pair<BasicRule, Integer> p : adornedRules) {
			magicRules.addAll(makeMagicRules(p.fst(), p.snd()));
		}
		return magicRules;
	}

	private boolean exploreTopDown(RelationSymbol sym) {
		if (sym instanceof AdornedSymbol) {
			sym = ((AdornedSymbol) sym).getBaseSymbol();
		}
		if (!sym.isIdbSymbol()) {
			return false;
		}
		return sym.isTopDown() || (topDownIsDefault && !sym.isBottomUp());
	}

	private Set<BasicRule> makeMagicRules(BasicRule r, int number) {
		int[] supCount = { 0 };
		Set<BasicRule> magicRules = new HashSet<>();
		List<Set<Var>> liveVarsByAtom = liveVarsByAtom(r);
		List<ComplexLiteral> l = new ArrayList<>();
		UserPredicate head = r.getHead();
		Set<Var> curLiveVars = new HashSet<>();
		if (exploreTopDown(head.getSymbol())) {
			UserPredicate inputAtom = createInputAtom(head);
			l.add(inputAtom);
			curLiveVars.addAll(inputAtom.varSet());
		}
		int i = 0;
		for (ComplexLiteral a : r) {
			Set<Var> futureLiveVars = liveVarsByAtom.get(i);
			Set<Var> nextLiveVars = curLiveVars.stream().filter(futureLiveVars::contains).collect(Collectors.toSet());
			l = a.accept(new ComplexLiteralVisitor<List<ComplexLiteral>, List<ComplexLiteral>>() {

				@Override
				public List<ComplexLiteral> visit(UnificationPredicate unificationPredicate, List<ComplexLiteral> l) {
					l.add(a);
					return l;
				}

				@Override
				public List<ComplexLiteral> visit(UserPredicate userPredicate, List<ComplexLiteral> l) {
					RelationSymbol sym = userPredicate.getSymbol();
					if (exploreTopDown(sym)) {
						Set<Var> supVars = a.varSet().stream().filter(curLiveVars::contains)
								.collect(Collectors.toSet());
						supVars.addAll(nextLiveVars);
						UserPredicate supAtom = createSupAtom(supVars, number, supCount[0], head.getSymbol());
						magicRules.add(BasicRule.make(supAtom, l));
						magicRules.add(
								BasicRule.make(createInputAtom(userPredicate), Collections.singletonList(supAtom)));
						l = new ArrayList<>();
						l.add(supAtom);
						l.add(a);
						supCount[0]++;
					} else {
						l.add(a);
					}
					return l;
				}

			}, l);
			curLiveVars.clear();
			curLiveVars.addAll(nextLiveVars);
			for (Var v : a.varSet()) {
				if (futureLiveVars.contains(v)) {
					curLiveVars.add(v);
				}
			}
			i++;
		}
		magicRules.add(BasicRule.make(head, l));
		return magicRules;
	}

	private List<Set<Var>> liveVarsByAtom(BasicRule r) {
		List<Set<Var>> liveVars = new ArrayList<>();
		Set<Var> acc = r.getHead().varSet();
		liveVars.add(acc);
		for (int i = r.getBodySize() - 1; i > 0; i--) {
			acc = new HashSet<>(acc);
			acc.addAll(r.getBody(i).varSet());
			liveVars.add(acc);
		}
		Collections.reverse(liveVars);
		return liveVars;
	}

	private UserPredicate createSupAtom(Set<Var> curLiveVars, int ruleNum, int supCount, Symbol headSym) {
		List<Term> l = new ArrayList<>(curLiveVars);
		l.sort(new Comparator<Term>() {

			@Override
			public int compare(Term o1, Term o2) {
				return o1.toString().compareTo(o2.toString());
			}

		});
		Term[] args = l.toArray(new Term[0]);
		SupSymbol supSym = new SupSymbol(ruleNum, supCount, args.length);
		return UserPredicate.make(supSym, args, false);
	}

	private UserPredicate createInputAtom(UserPredicate a) {
		AdornedSymbol headSym = (AdornedSymbol) a.getSymbol();
		InputSymbol inputSym = new InputSymbol(headSym);
		Term[] inputArgs = new Term[inputSym.getArity()];
		Term[] args = a.getArgs();
		boolean[] adornment = headSym.getAdornment();
		for (int i = 0, j = 0; i < args.length; i++) {
			if (adornment[i]) {
				inputArgs[j] = args[i];
				j++;
			}
		}
		return UserPredicate.make(inputSym, inputArgs, false);
	}

	public static class SupSymbol implements RelationSymbol {

		private final int ruleNum;
		private final int supCount;
		private final int arity;

		public SupSymbol(int ruleNum, int supCount, int arity) {
			this.ruleNum = ruleNum;
			this.supCount = supCount;
			this.arity = arity;
		}

		@Override
		public int getArity() {
			return arity;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + arity;
			result = prime * result + ruleNum;
			result = prime * result + supCount;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			SupSymbol other = (SupSymbol) obj;
			if (arity != other.arity)
				return false;
			if (ruleNum != other.ruleNum)
				return false;
			if (supCount != other.supCount)
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "sup_" + ruleNum + "_" + supCount;
		}

		@Override
		public FunctorType getCompileTimeType() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isIdbSymbol() {
			return true;
		}

		@Override
		public boolean isDisk() {
			return false;
		}

		@Override
		public boolean isBottomUp() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isTopDown() {
			throw new UnsupportedOperationException();
		}

	}

	public static class InputSymbol extends AbstractWrappedRelationSymbol<AdornedSymbol> {

		private final int arity;

		public InputSymbol(AdornedSymbol baseSymbol) {
			super(baseSymbol);
			int nbound = 0;
			for (boolean b : getBaseSymbol().getAdornment()) {
				nbound += b ? 1 : 0;
			}
			arity = nbound;
		}

		@Override
		public int getArity() {
			return arity;
		}

		@Override
		public String toString() {
			return "input_" + getBaseSymbol();
		}

		@Override
		public FunctorType getCompileTimeType() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isBottomUp() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isTopDown() {
			throw new UnsupportedOperationException();
		}

	}

	private boolean isStratified(BasicProgram p) {
		try {
			Stratifier stratifier = new Stratifier(p);
			for (Stratum s : stratifier.stratify()) {
				if (s.hasRecursiveNegationOrAggregation()) {
					return false;
				}
			}
			return true;
		} catch (InvalidProgramException e) {
			return false;
		}
	}

	private Set<BasicRule> adjustAdornedRules(Collection<BasicRule> adRules) {
		Set<BasicRule> newRules = new HashSet<>();
		for (BasicRule r : adRules) {
			UserPredicate head = r.getHead();
			if (exploreTopDown(head.getSymbol())) {
				List<ComplexLiteral> body = new ArrayList<>();
				body.add(createInputAtom(head));
				r.forEach(body::add);
				newRules.add(BasicRule.make(head, body));
			} else {
				newRules.add(r);
			}
		}
		return newRules;
	}

	private ProgramImpl stratify(BasicProgram p, Set<BasicRule> adornedRules) throws InvalidProgramException {
		Set<BasicRule> newRules = new HashSet<>();
		for (RelationSymbol sym : p.getRuleSymbols()) {
			for (BasicRule r : p.getRules(sym)) {
				UserPredicate head = makePositive(r.getHead());
				List<ComplexLiteral> body = makePositive(r);
				newRules.add(BasicRule.make(head, body));
			}
		}
		newRules.addAll(adjustAdornedRules(adornedRules));
		return new ProgramImpl(newRules, p.getQuery());
	}

	private <C extends ComplexLiteral> C makePositive(C atom) {
		return atom.accept(new ComplexLiteralVisitor<Void, C>() {

			@SuppressWarnings("unchecked")
			@Override
			public C visit(UnificationPredicate unificationPredicate, Void input) {
				return (C) unificationPredicate;
			}

			@SuppressWarnings("unchecked")
			@Override
			public C visit(UserPredicate userPredicate, Void input) {
				RelationSymbol sym = userPredicate.getSymbol();
				if (sym.isIdbSymbol() && !(sym instanceof InputSymbol || sym instanceof SupSymbol)) {
					if (userPredicate.isNegated()) {
						return null;
					}
					userPredicate = UserPredicate.make(new PositiveSymbol(sym), userPredicate.getArgs(), false);
				}
				return (C) userPredicate;
			}

		}, null);
	}

	private List<ComplexLiteral> makePositive(Iterable<ComplexLiteral> atoms) {
		List<ComplexLiteral> l = new ArrayList<>();
		for (ComplexLiteral a : atoms) {
			ComplexLiteral b = makePositive(a);
			if (b != null) {
				l.add(b);
			}
		}
		return l;
	}

	private static class PositiveSymbol extends AbstractWrappedRelationSymbol<RelationSymbol> {

		public PositiveSymbol(RelationSymbol baseSymbol) {
			super(baseSymbol);
		}

		@Override
		public String toString() {
			return "p_" + getBaseSymbol();
		}

		@Override
		public FunctorType getCompileTimeType() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isBottomUp() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isTopDown() {
			throw new UnsupportedOperationException();
		}

	}

	private static class HiddenPredicateFinder {

		private final Program<UserPredicate, BasicRule> origProg;
		private final Set<FunctionSymbol> visitedFunctions = new HashSet<>();
		private final Set<RelationSymbol> seenPredicates = new HashSet<>();

		public HiddenPredicateFinder(Program<UserPredicate, BasicRule> origProg) {
			this.origProg = origProg;
		}

		private void findHiddenPredicates(Term t, Set<RelationSymbol> s) {
			t.accept(predicatesInTermExtractor, s);
		}

		public Set<RelationSymbol> allSeenPredicates() {
			return seenPredicates;
		}

		public Set<RelationSymbol> visit(UserFunctionDef def) {
			Set<RelationSymbol> s = new HashSet<>();
			if (visitedFunctions.add(def.getSymbol())) {
				findHiddenPredicates(def.getBody(), s);
			}
			return s;
		}

		private void visit(ComplexLiteral l, Set<RelationSymbol> s) {
			l.accept(new ComplexLiteralVisitor<Void, Void>() {

				@Override
				public Void visit(UnificationPredicate unificationPredicate, Void input) {
					findHiddenPredicates(unificationPredicate.getLhs(), s);
					findHiddenPredicates(unificationPredicate.getRhs(), s);
					return null;
				}

				@Override
				public Void visit(UserPredicate userPredicate, Void input) {
					for (Term t : userPredicate.getArgs()) {
						findHiddenPredicates(t, s);
					}
					return null;
				}

			}, null);
		}

		public Set<RelationSymbol> visit(Rule<? extends ComplexLiteral, ? extends ComplexLiteral> rule) {
			Set<RelationSymbol> s = new HashSet<>();
			visit(rule.getHead(), s);
			for (ComplexLiteral l : rule) {
				visit(l, s);
			}
			return s;
		}

		private TermVisitor<Set<RelationSymbol>, Void> predicatesInTermExtractor = new TermVisitor<Set<RelationSymbol>, Void>() {

			@Override
			public Void visit(Var t, Set<RelationSymbol> in) {
				return null;
			}

			@Override
			public Void visit(Constructor c, Set<RelationSymbol> in) {
				for (Term t : c.getArgs()) {
					t.accept(this, in);
				}
				return null;
			}

			@Override
			public Void visit(Primitive<?> p, Set<RelationSymbol> in) {
				return null;
			}

			@Override
			public Void visit(Expr e, Set<RelationSymbol> in) {
				e.accept(predicatesInExprExtractor, in);
				return null;
			}

		};

		private ExprVisitor<Set<RelationSymbol>, Void> predicatesInExprExtractor = new ExprVisitor<Set<RelationSymbol>, Void>() {

			@Override
			public Void visit(MatchExpr matchExpr, Set<RelationSymbol> in) {
				matchExpr.getMatchee().accept(predicatesInTermExtractor, in);
				for (MatchClause cl : matchExpr) {
					cl.getRhs().accept(predicatesInTermExtractor, in);
				}
				return null;
			}

			@Override
			public Void visit(FunctionCall funcCall, Set<RelationSymbol> in) {
				FunctionSymbol sym = funcCall.getSymbol();
				if (visitedFunctions.add(sym)) {
					if (sym instanceof PredicateFunctionSymbol) {
						RelationSymbol psym = ((PredicateFunctionSymbol) sym).getPredicateSymbol();
						seenPredicates.add(psym);
						in.add(psym);
					}
					FunctionDef def = origProg.getDef(sym);
					if (def instanceof UserFunctionDef) {
						((UserFunctionDef) def).getBody().accept(predicatesInTermExtractor, in);
					}
				}
				for (Term t : funcCall.getArgs()) {
					t.accept(predicatesInTermExtractor, in);
				}
				return null;
			}

			@Override
			public Void visit(LetFunExpr funcDef, Set<RelationSymbol> in) {
				throw new AssertionError("impossible");
			}

			@Override
			public Void visit(Fold fold, Set<RelationSymbol> in) {
				fold.getShamCall().accept(this, in);
				return null;
			}

		};

	}

	private class ProgramImpl implements BasicProgram {

		private final Map<RelationSymbol, Set<BasicRule>> rules = new HashMap<>();
		private final Map<RelationSymbol, Set<Term[]>> facts = new HashMap<>();
		private final UserPredicate query;

		public ProgramImpl(Set<BasicRule> rs, UserPredicate query) throws InvalidProgramException {
			SymbolManager sm = origProg.getSymbolManager();
			HiddenPredicateFinder hpf = new HiddenPredicateFinder(origProg);
			for (BasicRule r : rs) {
				RelationSymbol headSym = r.getHead().getSymbol();
				Util.lookupOrCreate(rules, headSym, HashSet::new).add(r);
				sm.registerSymbol(headSym);
				for (ComplexLiteral l : r) {
					if (l instanceof UserPredicate) {
						RelationSymbol sym = ((UserPredicate) l).getSymbol();
						sm.registerSymbol(sym);
						if (sym.isEdbSymbol()) {
							facts.putIfAbsent(sym, origProg.getFacts(sym));
						} else {
							rules.putIfAbsent(sym, new HashSet<>());
						}
					}
				}
				hpf.visit(r);
			}
			for (FunctionSymbol sym : origProg.getFunctionSymbols()) {
				FunctionDef def = origProg.getDef(sym);
				if (def instanceof UserFunctionDef) {
					hpf.visit((UserFunctionDef) def);
				}
			}
			for (RelationSymbol psym : hpf.allSeenPredicates()) {
				if (exploreTopDown(psym)) {
					throw new InvalidProgramException("Cannot refer to top-down IDB predicate " + psym
							+ " in a function; consider annotating " + psym + " with @bottomup");
				}
				if (psym.isEdbSymbol()) {
					facts.putIfAbsent(psym, origProg.getFacts(psym));
				}
				if (psym.isIdbSymbol()) {
					rules.putIfAbsent(psym, new HashSet<>());
				}
			}
			// Do not keep unnecessary facts around if there is a query.
			if (query == null) {
				for (RelationSymbol sym : origProg.getFactSymbols()) {
					facts.putIfAbsent(sym, origProg.getFacts(sym));
				}
			}
			this.query = query;
		}

		@Override
		public Set<FunctionSymbol> getFunctionSymbols() {
			return origProg.getFunctionSymbols();
		}

		@Override
		public Set<RelationSymbol> getFactSymbols() {
			return Collections.unmodifiableSet(facts.keySet());
		}

		@Override
		public Set<RelationSymbol> getRuleSymbols() {
			return Collections.unmodifiableSet(rules.keySet());
		}

		@Override
		public FunctionDef getDef(FunctionSymbol sym) {
			return origProg.getDef(sym);
		}

		@Override
		public Set<Term[]> getFacts(RelationSymbol sym) {
			assert sym.isEdbSymbol();
			return Util.lookupOrCreate(facts, sym, () -> Collections.emptySet());
		}

		@Override
		public Set<BasicRule> getRules(RelationSymbol sym) {
			assert sym.isIdbSymbol();
			return Util.lookupOrCreate(rules, sym, () -> Collections.emptySet());
		}

		@Override
		public SymbolManager getSymbolManager() {
			return origProg.getSymbolManager();
		}

		@Override
		public boolean hasQuery() {
			return query != null;
		}

		@Override
		public UserPredicate getQuery() {
			return query;
		}

		@Override
		public FunctionCallFactory getFunctionCallFactory() {
			return origProg.getFunctionCallFactory();
		}

		@Override
		public Set<ConstructorSymbol> getUninterpretedFunctionSymbols() {
			return origProg.getUninterpretedFunctionSymbols();
		}

		@Override
		public Set<TypeSymbol> getTypeSymbols() {
			return origProg.getTypeSymbols();
		}

	}

}
