package edu.harvard.seas.pl.formulog.magic;

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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Annotation;
import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.Z3ThreadFactory;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.DedupWorkList;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;

public class MagicSetTransformer {

	private final Program origProg;
	private boolean topDownIsDefault;

	private static final boolean debug = System.getProperty("debugMst") != null;

	public MagicSetTransformer(Program prog) {
		this.origProg = prog;
	}

	public synchronized Pair<Program, Atom> transform(Atom query, boolean useDemandTransformation)
			throws InvalidProgramException {
		topDownIsDefault = true;
		if (query.isNegated()) {
			throw new InvalidProgramException("Query cannot be negated");
		}
		Symbol qsym = query.getSymbol();
		if (qsym.getSymbolType().equals(SymbolType.SPECIAL_REL)) {
			throw new InvalidProgramException("Cannot query built-in predicate: " + query.getSymbol());
		}
		query = normalizeQuery(query);
		Program newProg;
		if (query.getSymbol().getSymbolType().isEDBSymbol()) {
			newProg = makeEdbProgram(query);
		} else {
			Atom adornedQuery = Adornments.adorn(query, Collections.emptySet(), origProg, topDownIsDefault);
			Set<Rule> adRules = adorn(Collections.singleton(adornedQuery.getSymbol()));
			Set<Rule> magicRules = makeMagicRules(adRules);
			magicRules.add(makeSeedRule(adornedQuery));
			Program magicProg = new ProgramImpl(magicRules, origProg, false);
			if (!isStratified(magicProg)) {
				magicProg = stratify(magicProg, adRules);
			}
			if (useDemandTransformation) {
				magicProg = stripAdornments(magicProg);
			} else {
				query = adornedQuery;
			}
			newProg = magicProg;
		}
		return new Pair<>(newProg, query);
	}

	public Atom normalizeQuery(final Atom query) throws InvalidProgramException {
		ForkJoinPool fjp = new ForkJoinPool(1, new Z3ThreadFactory(origProg.getSymbolManager()), null, true);
		@SuppressWarnings("serial")
		Atom query2 = fjp.invoke(new RecursiveTask<Atom>() {

			@Override
			protected Atom compute() {
				try {
					return Atoms.normalize(query);
				} catch (EvaluationException e) {
					return null;
				}
			}

		});
		fjp.shutdown();
		while (true) {
			try {
				if (fjp.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS)) {
					break;
				}
			} catch (InterruptedException e) {
				// loop
			}
		}
		if (query2 == null) {
			throw new InvalidProgramException("Query contained function call that could not be normalized: " + query);
		}
		return query;
	}

	private Rule makeSeedRule(Atom adornedQuery) {
		return BasicRule.get(createInputAtom(adornedQuery));
	}

	private Program makeEdbProgram(Atom query) {
		Symbol querySym = query.getSymbol();
		Set<Atom> facts = new HashSet<>();
		for (Atom fact : origProg.getFacts(querySym)) {
			try {
				if (Unification.unify(query, fact, new SimpleSubstitution())) {
					facts.add(fact);
				}
			} catch (EvaluationException e) {
				throw new AssertionError("impossible");
			}
		}
		return new Program() {

			@Override
			public Set<Symbol> getFunctionSymbols() {
				return Collections.emptySet();
			}

			@Override
			public Set<Symbol> getFactSymbols() {
				return Collections.singleton(querySym);
			}

			@Override
			public Set<Symbol> getRuleSymbols() {
				return Collections.emptySet();
			}

			@Override
			public FunctionDef getDef(Symbol sym) {
				throw new IllegalArgumentException("No definition for function with symbol: " + sym);
			}

			@Override
			public Set<Atom> getFacts(Symbol sym) {
				if (querySym.equals(sym)) {
					return facts;
				}
				return Collections.emptySet();
			}

			@Override
			public Set<Rule> getRules(Symbol sym) {
				return Collections.emptySet();
			}

			@Override
			public SymbolManager getSymbolManager() {
				return origProg.getSymbolManager();
			}

			@Override
			public Set<Annotation> getAnnotations(Symbol sym) {
				return origProg.getAnnotations(sym);
			}

		};
	}

	public synchronized Program transform(boolean useDemandTransformation) throws InvalidProgramException {
		topDownIsDefault = false;
		Set<Symbol> bottomUpSymbols = new HashSet<>();
		for (Symbol sym : origProg.getRuleSymbols()) {
			if (!origProg.getAnnotations(sym).contains(Annotation.TOPDOWN)) {
				bottomUpSymbols.add(sym);
			}
		}
		Set<Rule> adRules = adorn(bottomUpSymbols);
		Set<Rule> magicRules = makeMagicRules(adRules);
		Program magicProg = new ProgramImpl(magicRules, origProg, true);
		if (!isStratified(magicProg)) {
			magicProg = stratify(magicProg, adRules);
		}
		if (useDemandTransformation) {
			magicProg = stripAdornments(magicProg);
		}
		return magicProg;
	}

	private static Program stripAdornments(Program prog) {
		Set<Rule> rules = new HashSet<>();
		for (Symbol sym : prog.getRuleSymbols()) {
			for (Rule r : prog.getRules(sym)) {
				List<Atom> newHead = new ArrayList<>();
				for (Atom atom : r.getHead()) {
					newHead.add(stripAdornment(atom));
				}
				List<Atom> newBody = new ArrayList<>();
				for (Atom atom : r.getBody()) {
					newBody.add(stripAdornment(atom));
				}
				rules.add(BasicRule.get(newHead, newBody));
			}
		}
		return new ProgramImpl(rules, prog, true);
	}

	private static Atom stripAdornment(Atom atom) {
		Symbol sym = atom.getSymbol();
		if (sym instanceof PositiveSymbol) {
			sym = ((PositiveSymbol) sym).getUnderlyingSymbol();
			assert sym instanceof AdornedSymbol;
			sym = new PositiveSymbol(((AdornedSymbol) sym).getSymbol());
		} else if (sym instanceof AdornedSymbol) {
			sym = ((AdornedSymbol) sym).getSymbol();
		}
		return Atoms.get(sym, atom.getArgs(), atom.isNegated());
	}

	private Set<Rule> adorn(Set<Symbol> seeds) throws InvalidProgramException {
		Set<Rule> adRules = new HashSet<>();
		DedupWorkList<Symbol> worklist = new DedupWorkList<>();
		for (Symbol seed : seeds) {
			worklist.push(seed);
		}
		while (!worklist.isEmpty()) {
			Symbol adSym = worklist.pop();
			Symbol origSym = adSym;
			if (adSym instanceof AdornedSymbol) {
				origSym = ((AdornedSymbol) adSym).getSymbol();
			}
			for (Rule r : origProg.getRules(origSym)) {
				for (Atom head : r.getHead()) {
					if (head.getSymbol().equals(origSym)) {
						Atom adHead = Atoms.get(adSym, head.getArgs(), head.isNegated());
						Rule adRule = Adornments.adornRule(adHead, Util.iterableToList(r.getBody()), origProg,
								topDownIsDefault);
						for (Atom a : adRule.getBody()) {
							Symbol sym = a.getSymbol();
							if (sym.getSymbolType().isIDBSymbol()) {
								worklist.push(sym);
							}
						}
						if (debug) {
							System.err.println(adRule);
						}
						adRules.add(adRule);
					}
				}
			}
		}
		return adRules;
	}

	private Set<Rule> makeMagicRules(Set<Rule> adornedRules) {
		Set<Rule> magicRules = new HashSet<>();
		int ruleNum = 0;
		for (Rule adornedRule : adornedRules) {
			magicRules.addAll(makeMagicRules(adornedRule, ruleNum));
			ruleNum++;
		}
		return magicRules;
	}

	private boolean exploreTopDown(Symbol sym) {
		if (sym instanceof AdornedSymbol) {
			sym = ((AdornedSymbol) sym).getSymbol();
		}
		if (!sym.getSymbolType().isIDBSymbol()) {
			return false;
		}
		Set<Annotation> annos = origProg.getAnnotations(sym);
		return annos.contains(Annotation.TOPDOWN) || (topDownIsDefault && !annos.contains(Annotation.BOTTOMUP));
	}

	private Set<Rule> makeMagicRules(Rule r, int number) {
		int supCount = 0;
		Set<Rule> magicRules = new HashSet<>();
		List<Set<Var>> liveVarsByAtom = liveVarsByAtom(r);
		List<Atom> l = new ArrayList<>();
		assert r.getHeadSize() == 1;
		Atom head = r.getHead(0);
		Set<Var> curLiveVars = new HashSet<>();
		if (exploreTopDown(head.getSymbol())) {
			Atom inputAtom = createInputAtom(head);
			l.add(inputAtom);
			curLiveVars.addAll(Atoms.varSet(inputAtom));
		}
		int i = 0;
		for (Atom a : r.getBody()) {
			Set<Var> futureLiveVars = liveVarsByAtom.get(i);
			Set<Var> nextLiveVars = curLiveVars.stream().filter(futureLiveVars::contains).collect(Collectors.toSet());
			Symbol sym = a.getSymbol();
			if (exploreTopDown(sym)) {
				Set<Var> supVars = Atoms.varSet(a).stream().filter(curLiveVars::contains).collect(Collectors.toSet());
				supVars.addAll(nextLiveVars);
				Atom supAtom = createSupAtom(supVars, number, supCount);
				magicRules.add(BasicRule.get(supAtom, l));
				magicRules.add(BasicRule.get(createInputAtom(a), Collections.singletonList(supAtom)));
				l = new ArrayList<>();
				l.add(supAtom);
				l.add(a);
				supCount++;
			} else {
				l.add(a);
			}
			curLiveVars = nextLiveVars;
			for (Var v : Atoms.varSet(a)) {
				if (futureLiveVars.contains(v)) {
					curLiveVars.add(v);
				}
			}
			i++;
		}
		magicRules.add(BasicRule.get(head, l));
		return magicRules;
	}

	private List<Set<Var>> liveVarsByAtom(Rule r) {
		List<Set<Var>> liveVars = new ArrayList<>();
		assert r.getHeadSize() == 1;
		Set<Var> acc = Atoms.varSet(r.getHead(0));
		liveVars.add(acc);
		for (int i = r.getBodySize() - 1; i > 0; i--) {
			acc.addAll(Atoms.varSet(r.getBody(i)));
			liveVars.add(acc);
		}
		Collections.reverse(liveVars);
		return liveVars;
	}

	private static Atom createSupAtom(Set<Var> curLiveVars, int ruleNum, int supCount) {
		Term[] args = (new ArrayList<>(curLiveVars)).toArray(new Term[0]);
		SupSymbol sym = new SupSymbol(ruleNum, supCount, args.length);
		return Atoms.getPositive(sym, args);
	}

	private static Atom createInputAtom(Atom a) {
		AdornedSymbol sym = (AdornedSymbol) a.getSymbol();
		InputSymbol inputSym = new InputSymbol(sym);
		Term[] inputArgs = new Term[inputSym.getArity()];
		Term[] args = a.getArgs();
		boolean[] adornment = sym.getAdornment();
		for (int i = 0, j = 0; i < args.length; i++) {
			if (adornment[i]) {
				inputArgs[j] = args[i];
				j++;
			}
		}
		return Atoms.getPositive(inputSym, inputArgs);
	}

	private static class SupSymbol implements Symbol {

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
		public SymbolType getSymbolType() {
			return SymbolType.IDB_REL;
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
		public Type getCompileTimeType() {
			throw new UnsupportedOperationException();
		}

	}

	private static class InputSymbol implements Symbol {

		private final AdornedSymbol underlyingSymbol;

		public InputSymbol(AdornedSymbol underlyingSymbol) {
			this.underlyingSymbol = underlyingSymbol;
		}

		@Override
		public int getArity() {
			int nbound = 0;
			for (boolean b : underlyingSymbol.getAdornment()) {
				nbound += b ? 1 : 0;
			}
			return nbound;
		}

		@Override
		public SymbolType getSymbolType() {
			return SymbolType.IDB_REL;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((underlyingSymbol == null) ? 0 : underlyingSymbol.hashCode());
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
			InputSymbol other = (InputSymbol) obj;
			if (underlyingSymbol == null) {
				if (other.underlyingSymbol != null)
					return false;
			} else if (!underlyingSymbol.equals(other.underlyingSymbol))
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "input_" + underlyingSymbol;
		}

		@Override
		public Type getCompileTimeType() {
			throw new UnsupportedOperationException();
		}

	}

	private boolean isStratified(Program p) {
		try {
			(new Stratifier(p)).stratify();
			return true;
		} catch (InvalidProgramException e) {
			return false;
		}
	}

	private Set<Rule> adjustAdornedRules(Set<Rule> adRules) {
		Set<Rule> newRules = new HashSet<>();
		for (Rule r : adRules) {
			assert r.getHeadSize() == 1;
			Atom head = r.getHead(0);
			if (exploreTopDown(head.getSymbol())) {
				List<Atom> body = new ArrayList<>();
				body.add(createInputAtom(head));
				r.getBody().forEach(body::add);
				newRules.add(BasicRule.get(head, body));
			} else {
				newRules.add(r);
			}
		}
		return newRules;
	}

	private ProgramImpl stratify(Program p, Set<Rule> adornedRules) {
		Set<Rule> newRules = new HashSet<>();
		for (Symbol sym : p.getRuleSymbols()) {
			for (Rule r : p.getRules(sym)) {
				assert r.getHeadSize() == 1;
				List<Atom> head = makePositive(r.getHead());
				List<Atom> body = makePositive(r.getBody());
				newRules.add(BasicRule.get(head, body));
			}
		}
		newRules.addAll(adjustAdornedRules(adornedRules));
		return new ProgramImpl(newRules, origProg, true);
	}

	private List<Atom> makePositive(Iterable<Atom> atoms) {
		List<Atom> l = new ArrayList<>();
		for (Atom a : atoms) {
			Symbol sym = a.getSymbol();
			if (sym instanceof AdornedSymbol) {
				if (a.isNegated()) {
					continue;
				}
				a = Atoms.getPositive(new PositiveSymbol(sym), a.getArgs());
			}
			l.add(a);
		}
		return l;
	}

	private static class PositiveSymbol implements Symbol {

		private final Symbol underlyingSymbol;

		public PositiveSymbol(Symbol underlyingSymbol) {
			this.underlyingSymbol = underlyingSymbol;
		}

		public Symbol getUnderlyingSymbol() {
			return underlyingSymbol;
		}

		@Override
		public int getArity() {
			return underlyingSymbol.getArity();
		}

		@Override
		public SymbolType getSymbolType() {
			return SymbolType.IDB_REL;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((underlyingSymbol == null) ? 0 : underlyingSymbol.hashCode());
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
			PositiveSymbol other = (PositiveSymbol) obj;
			if (underlyingSymbol == null) {
				if (other.underlyingSymbol != null)
					return false;
			} else if (!underlyingSymbol.equals(other.underlyingSymbol))
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "p_" + underlyingSymbol;
		}

		@Override
		public Type getCompileTimeType() {
			throw new UnsupportedOperationException();
		}

	}

	private static class ProgramImpl implements Program {

		private final Map<Symbol, Set<Rule>> rules = new HashMap<>();
		private final Map<Symbol, Set<Atom>> facts = new HashMap<>();
		private final boolean keepAllFacts;

		public final Program origProg;

		public ProgramImpl(Set<Rule> rs, Program origProg, boolean keepAllFacts) {
			for (Rule r : rs) {
				for (Atom head : r.getHead()) {
					Util.lookupOrCreate(rules, head.getSymbol(), () -> new HashSet<>()).add(r);
				}
				if (!keepAllFacts) {
					for (Atom a : r.getBody()) {
						Symbol sym = a.getSymbol();
						if (sym.getSymbolType().isEDBSymbol()) {
							facts.putIfAbsent(sym, origProg.getFacts(sym));
						}
					}
				}
			}
			this.origProg = origProg;
			this.keepAllFacts = keepAllFacts;
		}

		@Override
		public Set<Symbol> getFunctionSymbols() {
			return origProg.getFunctionSymbols();
		}

		@Override
		public Set<Symbol> getFactSymbols() {
			if (keepAllFacts) {
				return origProg.getFactSymbols();
			}
			return Collections.unmodifiableSet(facts.keySet());
		}

		@Override
		public Set<Symbol> getRuleSymbols() {
			return Collections.unmodifiableSet(rules.keySet());
		}

		@Override
		public FunctionDef getDef(Symbol sym) {
			return origProg.getDef(sym);
		}

		@Override
		public Set<Atom> getFacts(Symbol sym) {
			assert sym.getSymbolType().isEDBSymbol();
			if (keepAllFacts) {
				return origProg.getFacts(sym);
			}
			return Util.lookupOrCreate(facts, sym, () -> Collections.emptySet());
		}

		@Override
		public Set<Rule> getRules(Symbol sym) {
			assert sym.getSymbolType().isIDBSymbol();
			return Util.lookupOrCreate(rules, sym, () -> Collections.emptySet());
		}

		@Override
		public SymbolManager getSymbolManager() {
			return origProg.getSymbolManager();
		}

		@Override
		public Set<Annotation> getAnnotations(Symbol sym) {
			return origProg.getAnnotations(sym);
		}

	}

}
