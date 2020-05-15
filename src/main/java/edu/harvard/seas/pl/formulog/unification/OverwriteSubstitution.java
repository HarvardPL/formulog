package edu.harvard.seas.pl.formulog.unification;

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


import java.util.HashMap;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;

public class OverwriteSubstitution implements Substitution {

	private final Map<Var, Term> m;

	public OverwriteSubstitution() {
		this(new HashMap<>());
	}
	
	private OverwriteSubstitution(Map<Var, Term> m) {
		this.m = m;
	}
	
	@Override
	public void put(Var v, Term t) {
		m.put(v, t);
	}

	@Override
	public Term get(Var v) {
		assert m.containsKey(v);
		return m.get(v);
	}

	@Override
	public boolean containsKey(Var v) {
		return m.containsKey(v);
	}

	@Override
	public Iterable<Var> iterateKeys() {
		return m.keySet();
	}

	public OverwriteSubstitution copy() {
		return new OverwriteSubstitution(new HashMap<>(m));
	}
	
	@Override
	public String toString() {
		return m.toString();
	}

}
