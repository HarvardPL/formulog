package formulog.unification;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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

import formulog.ast.Term;
import formulog.ast.Var;

public class SimpleSubstitution implements Substitution {

	private final Map<Var, Term> map = new HashMap<>();

	@Override
	public void put(Var v, Term t) {
		map.put(v, t);
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
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder("[");
		for (Map.Entry<Var, Term> e : map.entrySet()) {
			sb.append(e.getKey());
			sb.append(" -> ");
			sb.append(e.getValue());
			sb.append(" ");
		}
		sb.append("]");
		return sb.toString();
	}

}
