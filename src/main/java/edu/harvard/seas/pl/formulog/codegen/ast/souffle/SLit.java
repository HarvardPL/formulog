package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.HashSet;
import java.util.Set;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

public interface SLit {
	
	default Set<SVar> varSet() {
		Set<SVar> vars = new HashSet<>();
		varSet(vars);
		return vars;
	}
	
	void varSet(Set<SVar> vars);
	
}
