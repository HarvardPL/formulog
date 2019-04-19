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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class RuleSubstitution implements Substitution {

	private final Map<Var, Term> map = new HashMap<>();
	private final Collection<Var>[] varsPerIdx;
	private int curIdx;
	
	@SuppressWarnings("unchecked")
	public RuleSubstitution(Rule r) {
		varsPerIdx = new Collection[r.getBodySize()];
		Set<Var> seen = new HashSet<>();
		int idx = 0;
		for (Atom a : r.getBody()) {
			Set<Var> vars = Atoms.varSet(a);
			vars.removeAll(seen);
			varsPerIdx[idx] = new ArrayList<>(vars);
			seen.addAll(vars);
			++idx;
		}
	}

	private RuleSubstitution(Collection<Var>[] varsPerIdx) {
		this.varsPerIdx = varsPerIdx;
	}
	
	@Override
	public void put(Var v, Term t) {
		Term t2 = map.put(v, t);
		assert t2 == null || t2.equals(t);
	}

	@Override
	public Term get(Var v) {
		Term t = map.get(v);
		assert t != null;
		return t;
	}

	@Override
	public boolean containsKey(Var v) {
		return map.containsKey(v);
	}

	@Override
	public Iterable<Var> iterateKeys() {
		return map.keySet();
	}
	
	public RuleSubstitution fresh() {
		return new RuleSubstitution(varsPerIdx);
	}
	
	public void setToBefore(int atomIdx) {
		while (curIdx >= atomIdx) {
			for (Var v : varsPerIdx[curIdx]) {
				map.remove(v);
			}
			--curIdx;
		}
		curIdx = atomIdx;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("[ ");
		for (int i = 0; i < varsPerIdx.length; ++i) {
			if (i == curIdx) {
				sb.append("*");
			}
			sb.append(i + " ");
			for (Var v : varsPerIdx[i]) {
				sb.append(v + "->" + map.get(v) + " ");
			}
		}
		sb.append(" ]");
		return sb.toString();
	}

}
