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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.CompositeIterable;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class IndexedNonAggregateFactSet implements IndexedFactSet {

	private final Atom canonicalAtom;
	private final IndexEntry[] idxs;
	private final Map<Object, Object> map = new ConcurrentHashMap<>();

	public IndexedNonAggregateFactSet(NormalAtom q, Set<Var> boundVars) {
		Pair<Atom, Set<IndexEntry>> p = createCanonicalAtom(q, boundVars);
		canonicalAtom = p.fst();
		idxs = createIndex(p.snd(), boundVars);
	}

	@SuppressWarnings("unchecked")
	@Override
	public void add(NormalAtom fact) {
		assert Atoms.varSet(fact).isEmpty();
		Substitution s = new SimpleSubstitution();
		try {
			if (!Unification.unify(fact, canonicalAtom, s)) {
				return;
			}
		} catch (EvaluationException e) {
			throw new AssertionError("There should not be any function reduction.");
		}
		Map<Object, Object> m = map;
		for (IndexEntry e : idxs) {
			m = (Map<Object, Object>) Util.lookupOrCreate(m, s.get(e.getV()), () -> new ConcurrentHashMap<>());
		}
		m.put(fact, Boolean.TRUE);
	}

	@Override
	public Iterable<NormalAtom> query(Substitution s) throws EvaluationException {
		/*
		 * XXX This does not enforce that the substitution matches the index.
		 */
		List<Iterable<NormalAtom>> acc = new ArrayList<>();
		// query(map, s, 0, acc);
		SimpleSubstitution s2 = new SimpleSubstitution();
		for (Var v : s.iterateKeys()) {
			s2.put(v, s.get(v));
		}
		query(map, s2, 0, acc);
		Iterable<NormalAtom> iter = new CompositeIterable<>(acc);
		return iter;
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private void query(Map<Object, Object> m, Substitution s, int idx, Collection<Iterable<NormalAtom>> acc)
			throws EvaluationException {
		if (m == null) {
			return;
		}
		if (idx >= idxs.length) {
			acc.add((Set) m.keySet());
			return;
		}
		IndexEntry e = idxs[idx];
		Var v = e.getV();
		Expr expr = e.getE();
		if (s.containsKey(v) || expr != null) {
			Term t = (expr == null) ? s.get(v) : expr.normalize(s);
			m = (Map<Object, Object>) m.get(t);
			query(m, s, idx + 1, acc);
		} else {
			for (Map.Entry entry : m.entrySet()) {
				Term t = (Term) entry.getKey();
				s.put(v, t);
				query((Map<Object, Object>) entry.getValue(), s, idx + 1, acc);
			}
		}
	}

	private Pair<Atom, Set<IndexEntry>> createCanonicalAtom(NormalAtom q, Set<Var> boundVars) {
		/*
		 * We need to index a variable if (1) it appears in a non-binding position in
		 * the atom and is not in the set of initially bound variables or (2) it appears
		 * in a binding position in the atom and is in the set of initially bound
		 * variables.
		 * 
		 * We also replace each function call with a fresh variable that must also be
		 * indexed.
		 */
		Set<IndexEntry> idxs = new HashSet<>();
		Term[] args = q.getArgs();
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].visit(new TermVisitor<Void, Term>() {

				@Override
				public Term visit(Var t, Void in) {
					if (boundVars.contains(t)) {
						idxs.add(new IndexEntry(t, null));
					}
					return t;
				}

				@Override
				public Term visit(Constructor t, Void in) {
					Term[] args = t.getArgs();
					Term[] newArgs = new Term[args.length];
					for (int i = 0; i < args.length; ++i) {
						newArgs[i] = args[i].visit(this, null);
					}
					return t.copyWithNewArgs(newArgs);
				}

				@Override
				public Term visit(Primitive<?> prim, Void in) {
					return prim;
				}

				@Override
				public Term visit(Expr expr, Void in) {
					Var v = Var.getFresh();
					idxs.add(new IndexEntry(v, expr));
					for (Var vv : Terms.varSet(expr)) {
						if (!boundVars.contains(vv)) {
							idxs.add(new IndexEntry(vv, null));
						}
					}
					return v;
				}

			}, null);
		}

		Atom canonicalAtom = Atoms.getPositive(q.getSymbol(), newArgs);
		return new Pair<>(canonicalAtom, idxs);
	}

	private IndexEntry[] createIndex(Set<IndexEntry> idxSet, Set<Var> initBoundVar) {
		Set<Var> boundVar = new HashSet<>(initBoundVar);
		List<IndexEntry> idxs = new ArrayList<>();
		while (!idxSet.isEmpty()) {
			for (IndexEntry e : new HashSet<>(idxSet)) {
				Var v = e.getV();
				Expr expr = e.getE();
				if (expr == null || boundVar.containsAll(Terms.varSet(expr))) {
					boundVar.add(v);
					idxs.add(e);
				}
				idxSet.remove(e);
			}
		}
		return idxs.toArray(new IndexEntry[0]);
	}

	@Override
	public String toString() {
		String s = "IndexedFactSet(";
		s += canonicalAtom + ", ";
		s += Arrays.toString(idxs) + ")";
		return s;
	}

	private static class IndexEntry {

		private final Var v;
		private final Expr expr;

		public IndexEntry(Var v, Expr expr) {
			this.v = v;
			this.expr = expr;
		}

		public Var getV() {
			return v;
		}

		public Expr getE() {
			return expr;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((expr == null) ? 0 : expr.hashCode());
			result = prime * result + ((v == null) ? 0 : v.hashCode());
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
			IndexEntry other = (IndexEntry) obj;
			if (expr == null) {
				if (other.expr != null)
					return false;
			} else if (!expr.equals(other.expr))
				return false;
			if (v == null) {
				if (other.v != null)
					return false;
			} else if (!v.equals(other.v))
				return false;
			return true;
		}

		@Override
		public String toString() {
			String s = "IndexEntry(" + v;
			if (expr != null) {
				s += ", <expr>";
			}
			return s + ")";
		}

	}

}
