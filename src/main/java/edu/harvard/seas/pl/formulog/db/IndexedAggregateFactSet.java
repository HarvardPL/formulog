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

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;

public class IndexedAggregateFactSet implements IndexedFactSet {

	private final Var[] index;
	private final Var[] unboundIndex;
	private final Var aggVar;
	private final boolean aggVarIsBound;
	private final NormalAtom atom;

	private final Map<Key, Map<Key, Term>> map = new ConcurrentHashMap<>();

	public IndexedAggregateFactSet(NormalAtom atom, Set<Var> boundVars) {
		this.atom = atom;
		Term[] args = atom.getArgs();
		assert allVars(args);
		List<Var> bound = new ArrayList<>();
		List<Var> unbound = new ArrayList<>();
		for (int i = 0; i < args.length - 1; ++i) {
			Var x = (Var) args[i];
			if (boundVars.contains(x)) {
				bound.add(x);
			} else {
				unbound.add(x);
			}
		}
		aggVar = (Var) args[args.length - 1];
		aggVarIsBound = boundVars.contains(aggVar);
		index = bound.toArray(new Var[0]);
		unboundIndex = unbound.toArray(new Var[0]);
	}

	private IndexedAggregateFactSet(Var[] index, Var[] unboundIndex, Var aggVar, boolean aggVarIsBound, NormalAtom atom) {
		this.index = index;
		this.unboundIndex = unboundIndex;
		this.aggVar = aggVar;
		this.aggVarIsBound = aggVarIsBound;
		this.atom = atom;
	}
	
	@Override
	public IndexedAggregateFactSet makeCleanCopy() {
		return new IndexedAggregateFactSet(index, unboundIndex, aggVar, aggVarIsBound, atom);
	}

	private static boolean allVars(Term[] ts) {
		for (Term t : ts) {
			if (!(t instanceof Var)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public void add(NormalAtom fact) throws EvaluationException {
		Substitution s = new SimpleSubstitution();
		if (!Unification.unify(atom, fact, s)) {
			return;
		}
		Term agg = s.get(aggVar);
		Key primary = makePrimaryKey(s);
		Map<Key, Term> m = Util.lookupOrCreate(map, primary, () -> new ConcurrentHashMap<>());
		Key secondary = makeSecondaryKey(s);
		m.put(secondary, agg);
	}

	@Override
	public Iterable<NormalAtom> query(Substitution s) throws EvaluationException {
		Key primaryKey = makePrimaryKey(s);
		Map<Key, Term> m = Util.lookupOrCreate(map, primaryKey, () -> new ConcurrentHashMap<>());
		// XXX This is inefficient
		List<NormalAtom> atoms = new ArrayList<>();
		for (Map.Entry<Key, Term> e : m.entrySet()) {
			Term agg = e.getValue();
			Substitution s2 = new SimpleSubstitution();
			if (aggVarIsBound) {
				if (!agg.equals(s.get(aggVar))) {
					continue;
				}
				s2.put(aggVar, agg);
			}
			for (Var v : index) {
				s2.put(v, s.get(v));
			}
			Key secondaryKey = e.getKey();
			for (int i = 0; i < unboundIndex.length; ++i) {
				s2.put(unboundIndex[i], secondaryKey.getArr()[i]);
			}
			atoms.add((NormalAtom) Atoms.applySubstitution(atom, s2));
		}
		return atoms;
	}

	private Key makePrimaryKey(Substitution s) {
		Term[] arr = new Term[index.length];
		for (int i = 0; i < index.length; ++i) {
			arr[i] = s.get(index[i]);
		}
		return new Key(arr);
	}
	
	private Key makeSecondaryKey(Substitution s) {
		Term[] arr = new Term[unboundIndex.length];
		for (int i = 0; i < unboundIndex.length; ++i) {
			arr[i] = s.get(unboundIndex[i]);
		}
		return new Key(arr);
	}

}
