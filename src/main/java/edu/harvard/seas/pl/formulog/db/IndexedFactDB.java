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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Util;

public class IndexedFactDB {

	private final IndexedFactSet[] idxs;
	private final Map<Symbol, Set<NormalAtom>> factsBySym = new ConcurrentHashMap<>();

	private IndexedFactDB(IndexedFactSet[] idxs) {
		this.idxs = idxs;
	}

	public Iterable<Symbol> getSymbols() {
		return factsBySym.keySet().stream().sorted(SymbolComparator.INSTANCE).collect(Collectors.toList());
	}

	public Iterable<NormalAtom> query(Symbol sym) {
		return getAllForSym(sym);
	}

	public Iterable<NormalAtom> query(int idx, Substitution subst) throws EvaluationException {
		assert idx >= 0 && idx < idxs.length;
		return idxs[idx].query(subst);
	}

	public boolean add(NormalAtom fact) {
		if (!getAllForSym(fact.getSymbol()).add(fact)) {
			return false;
		}
		for (IndexedFactSet idx : idxs) {
			idx.add(fact);
		}
		return true;
	}

	public boolean hasFact(NormalAtom fact) {
		return getAllForSym(fact.getSymbol()).contains(fact);
	}
	
	private Set<NormalAtom> getAllForSym(Symbol sym) {
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
		for (int i = 0; i < idxs.length; ++i) {
			sb.append(i + ": " + idxs[i] + "\n");
		}
		return sb.toString();
	}

	public static class IndexedFactDBBuilder {

		private final List<IndexedFactSet> idxs = new ArrayList<>();

		public synchronized int addIndex(NormalAtom q, Set<Var> boundVars) {
			idxs.add(new IndexedFactSet(q, boundVars));
			return idxs.size() - 1;
		}

		public synchronized IndexedFactDB build() {
			return new IndexedFactDB(idxs.toArray(new IndexedFactSet[0]));
		}

	}

}
