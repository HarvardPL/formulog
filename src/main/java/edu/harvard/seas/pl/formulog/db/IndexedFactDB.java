package edu.harvard.seas.pl.formulog.db;

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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.RelationProperties;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class IndexedFactDB {

	private final IndexedNonAggregateFactSet[] nonAggregateIndices;
	private final IndexedAggregateFactSet[] aggregateIndices;
	private final Map<Symbol, Map<Key, Term>> aggregateFactsBySym = new ConcurrentHashMap<>();
	private final Map<Symbol, Set<NormalAtom>> factsBySym = new ConcurrentHashMap<>();
	private final Map<Symbol, Pair<FunctionDef, Term>> aggStuff;

	private IndexedFactDB(IndexedNonAggregateFactSet[] idxs, IndexedAggregateFactSet[] aggregateIndices,
			Map<Symbol, Pair<FunctionDef, Term>> aggStuff) {
		this.nonAggregateIndices = idxs;
		this.aggregateIndices = aggregateIndices;
		this.aggStuff = aggStuff;
		for (Symbol sym : this.aggStuff.keySet()) {
			aggregateFactsBySym.put(sym, new ConcurrentHashMap<>());
		}
	}

	public Iterable<Symbol> getSymbols() {
		Set<Symbol> syms = new HashSet<>(factsBySym.keySet());
		syms.addAll(aggregateFactsBySym.keySet());
		return syms.stream().sorted(SymbolComparator.INSTANCE).collect(Collectors.toList());
	}

	public Iterable<NormalAtom> query(Symbol sym) {
		if (aggregateFactsBySym.containsKey(sym)) {
			List<NormalAtom> atoms = new ArrayList<>();
			for (Map.Entry<Key, Term> e : aggregateFactsBySym.get(sym).entrySet()) {
				Term[] arr = e.getKey().getArr();
				Term[] args = new Term[arr.length + 1];
				for (int i = 0; i < arr.length; ++i) {
					args[i] = arr[i];
				}
				args[arr.length] = e.getValue();
				atoms.add((NormalAtom) Atoms.getPositive(sym, args));
			}
			return atoms;
		} else {
			return getAllForSym(sym);
		}
	}

	public Iterable<NormalAtom> query(int idx, Substitution subst) throws EvaluationException {
		if (idx < 0) {
			idx = -(idx + 1);
			return aggregateIndices[idx].query(subst);
		} else {
			return nonAggregateIndices[idx].query(subst);
		}
	}

	public boolean add(NormalAtom fact) throws EvaluationException {
		if (aggStuff.containsKey(fact.getSymbol())) {
			return addAggregate(fact);
		}
		if (!getAllForSym(fact.getSymbol()).add(fact)) {
			return false;
		}
		for (IndexedNonAggregateFactSet idx : nonAggregateIndices) {
			idx.add(fact);
		}
		return true;
	}
	
	public Term getClosestAggregateValue(NormalAtom aggFact) {
		Map<Key, Term> m = aggregateFactsBySym.get(aggFact.getSymbol());
		assert m != null;
		Key key = makeAggKey(aggFact);
		return m.get(key);
	}

	private Key makeAggKey(NormalAtom aggFact) {
		Term[] args = aggFact.getArgs();
		Term[] arr = new Term[args.length - 1];
		for (int i = 0; i < arr.length; ++i) {
			arr[i] = args[i];
		}
		return new Key(arr);
	}
	
	private boolean addAggregate(NormalAtom fact) throws EvaluationException {
		Symbol sym = fact.getSymbol();
		Term agg = fact.getArgs()[sym.getArity() - 1];
		Key key = makeAggKey(fact);
		Map<Key, Term> m = Util.lookupOrCreate(aggregateFactsBySym, sym, () -> new ConcurrentHashMap<>());
		Pair<FunctionDef, Term> p = aggStuff.get(sym);
		FunctionDef aggFunc = p.fst();
		Term aggInit = p.snd();

		if (!m.containsKey(key)) {
			agg = aggFunc.evaluate(new Term[] { agg, aggInit });
			Term oldAgg = m.putIfAbsent(key, agg);
			if (oldAgg == null) {
				addToAllAggregateIndices(fact, agg);
				return true;
			}
		}

		Term oldAgg;
		Term newAgg;
		do {
			oldAgg = m.get(key);
			newAgg = aggFunc.evaluate(new Term[] { agg, oldAgg });
		} while (!m.replace(key, oldAgg, newAgg));
		if (newAgg.equals(oldAgg)) {
			return false;
		}
		addToAllAggregateIndices(fact, newAgg);
		return true;
	}

	private void addToAllAggregateIndices(NormalAtom atom, Term agg) throws EvaluationException {
		Term[] args = atom.getArgs();
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length - 1; ++i) {
			newArgs[i] = args[i];
		}
		newArgs[args.length - 1] = agg;
		NormalAtom newAtom = (NormalAtom) Atoms.getPositive(atom.getSymbol(), newArgs);
		for (IndexedAggregateFactSet idx : aggregateIndices) {
			idx.add(newAtom);
		}
	}

	public boolean hasFact(NormalAtom fact) {
		Map<Key, Term> m = aggregateFactsBySym.get(fact.getSymbol());
		if (m != null) {
			Term[] args = fact.getArgs();
			Term[] arr = new Term[args.length - 1];
			for (int i = 0; i < arr.length; ++i) {
				arr[i] = args[i];
			}
			Term agg = m.get(new Key(arr));
			return args[arr.length].equals(agg);
		} else {
			return getAllForSym(fact.getSymbol()).contains(fact);
		}
	}

	private Set<NormalAtom> getAllForSym(Symbol sym) {
		assert !aggregateFactsBySym.containsKey(sym);
		return Util.lookupOrCreate(factsBySym, sym, () -> Util.concurrentSet());
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Symbol sym : getSymbols()) {
			for (NormalAtom a : query(sym)) {
				sb.append(a + "\n");
			}
		}
		for (int i = 0; i < nonAggregateIndices.length; ++i) {
			sb.append(i + ": " + nonAggregateIndices[i] + "\n");
		}
		return sb.toString();
	}

	public static class IndexedFactDBBuilder {

		private final Program prog;
		private final List<IndexedNonAggregateFactSet> nonAggregateIndices = new ArrayList<>();
		private final List<IndexedAggregateFactSet> aggregateIndices = new ArrayList<>();
		private final Map<Symbol, Pair<FunctionDef, Term>> aggStuff = new HashMap<>();

		public IndexedFactDBBuilder(Program prog) {
			this.prog = prog;
		}

		public synchronized int addIndex(NormalAtom q, Set<Var> boundVars) {
			Symbol sym = q.getSymbol();
			RelationProperties props = prog.getRelationProperties(sym);
			if (props.isAggregated()) {
				if (!aggStuff.containsKey(sym)) {
					FunctionDef def = prog.getDef(props.getAggFuncSymbol());
					aggStuff.put(sym, new Pair<>(def, props.getAggFuncInit()));
				}
				aggregateIndices.add(new IndexedAggregateFactSet(q, boundVars));
				return -aggregateIndices.size();
			} else {
				nonAggregateIndices.add(new IndexedNonAggregateFactSet(q, boundVars));
				return nonAggregateIndices.size() - 1;
			}
		}

		public synchronized IndexedFactDB build() {
			List<IndexedNonAggregateFactSet> nonAgg = nonAggregateIndices.stream()
					.map(IndexedNonAggregateFactSet::makeCleanCopy).collect(Collectors.toList());
			List<IndexedAggregateFactSet> agg = aggregateIndices.stream().map(IndexedAggregateFactSet::makeCleanCopy)
					.collect(Collectors.toList());
			return new IndexedFactDB(nonAgg.toArray(new IndexedNonAggregateFactSet[0]),
					agg.toArray(new IndexedAggregateFactSet[0]), aggStuff);
		}

	}

}
