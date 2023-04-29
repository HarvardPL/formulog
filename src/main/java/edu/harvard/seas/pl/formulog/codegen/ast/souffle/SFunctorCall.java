package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

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

import java.util.Arrays;
import java.util.List;
import java.util.Set;

public class SFunctorCall implements STerm {

	private final String func;
	private final List<STerm> args;

	public SFunctorCall(String func, List<STerm> args) {
		this.func = func;
		this.args = args;
	}

	public SFunctorCall(String func, STerm... args) {
		this(func, Arrays.asList(args));
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("@");
		sb.append(func);
		sb.append("(");
		for (int i = 0; i < args.size(); ++i) {
			sb.append(args.get(i));
			if (i < args.size() - 1) {
				sb.append(", ");
			}
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public void varSet(Set<SVar> vars) {
		for (var t : args) {
			t.varSet(vars);
		}
	}

}
