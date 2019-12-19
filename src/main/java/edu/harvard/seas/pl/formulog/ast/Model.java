package edu.harvard.seas.pl.formulog.ast;

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

import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.types.BuiltInTypesFactory;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class Model extends AbstractTerm implements Primitive<Map<SolverVariable, Term>> {

	private static final Map<Map<SolverVariable, Term>, Model> memo = new ConcurrentHashMap<>();
	
	private final Map<SolverVariable, Term> m;

	private Model(Map<SolverVariable, Term> m) {
		this.m = m;
	}

	public static Model make(Map<SolverVariable, Term> m) {
		return Util.lookupOrCreate(memo, m, () -> new Model(m));
	}

	@Override
	public Map<SolverVariable, Term> getVal() {
		return m;
	}

	@Override
	public Type getType() {
		return BuiltInTypesFactory.model;
	}

	@Override
	public String toString() {
		String s = "[";
		for (Iterator<Map.Entry<SolverVariable, Term>> it = m.entrySet().iterator(); it.hasNext();) {
			Map.Entry<SolverVariable, Term> e = it.next();
			s += e.getKey() + " -> " + e.getValue();
			if (it.hasNext()) {
				s += ", ";
			}
		}
		return s + "]";
	}

}
