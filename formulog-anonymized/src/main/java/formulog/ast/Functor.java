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


import java.util.Map;
import java.util.Set;

import formulog.symbols.Symbol;

public interface Functor<S extends Symbol> extends Term {

	S getSymbol();

	Term[] getArgs();

	Term copyWithNewArgs(Term[] args);

	@Override
	default void varSet(Set<Var> acc) {
		if (!isGround()) {
			for (Term arg : getArgs()) {
				arg.varSet(acc);
			}
		}
	}
	
	@Override
	default void updateVarCounts(Map<Var, Integer> counts) {
		for (Term arg : getArgs()) {
			arg.updateVarCounts(counts);
		}
	}

}
