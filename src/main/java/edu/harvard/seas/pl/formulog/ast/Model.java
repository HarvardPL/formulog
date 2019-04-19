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

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public class Model implements Primitive<Map<SolverVariable, Term>> {

	private final Map<SolverVariable, Term> m;
	private Integer hashCode;

	private Model(Map<SolverVariable, Term> m) {
		this.m = m;
	}

	// I think this should be thread-safe, as long as m is not modified.
	public static Model make(Map<SolverVariable, Term> m) {
		return new Model(m);
	}

	@Override
	public Map<SolverVariable, Term> getVal() {
		return m;
	}

	@Override
	public Type getType() {
		return BuiltInTypes.model;
	}

	@Override
	public int hashCode() {
		if (hashCode == null) {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((m == null) ? 0 : m.hashCode());
			return (hashCode = result);
		} else {
			return hashCode;
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Model other = (Model) obj;
		if (m == null) {
			if (other.m != null)
				return false;
		} else if (!m.equals(other.m))
			return false;
		return true;
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
