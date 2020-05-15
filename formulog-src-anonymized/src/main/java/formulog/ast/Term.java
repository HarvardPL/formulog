package formulog.ast;

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


import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import formulog.ast.Terms.TermVisitor;
import formulog.ast.Terms.TermVisitorExn;
import formulog.eval.EvaluationException;
import formulog.unification.Substitution;

public interface Term {
	
	<I, O> O accept(TermVisitor<I, O> v, I in);
	
	<I, O, E extends Throwable> O accept(TermVisitorExn<I, O, E> v, I in) throws E;
	
	boolean isGround();

	boolean containsUnevaluatedTerm();

	Term applySubstitution(Substitution s);
	
	Term normalize(Substitution s) throws EvaluationException;
	
	void varSet(Set<Var> acc);
	
	default Set<Var> varSet() {
		Set<Var> vars = new HashSet<>();
		varSet(vars);
		return vars;
	}
	
	void updateVarCounts(Map<Var, Integer> counts);
	
	int getId();
	
}
