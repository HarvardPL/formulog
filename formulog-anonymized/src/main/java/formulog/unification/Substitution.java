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

import formulog.ast.Term;
import formulog.ast.Var;

public interface Substitution {
	
	void put(Var v, Term t);
	
	Term get(Var v);

	static Term getIfPresent(Term t, Substitution s) {
		if (t instanceof Var && s.containsKey((Var) t)) {
			return s.get((Var) t);
		}
		return t;
	}
	
	boolean containsKey(Var v);
	
	Iterable<Var> iterateKeys();

//	Substitution copy();
	
//	int newCheckpoint();

//	int getCheckpoint();

//	void revertTo(int checkpoint);

//	int popCheckpoint();

//	void mergeCheckpoint();
	
}
