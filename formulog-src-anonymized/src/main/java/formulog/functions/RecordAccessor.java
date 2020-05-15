package formulog.functions;

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

import formulog.ast.Constructor;
import formulog.ast.Term;
import formulog.eval.EvaluationException;
import formulog.symbols.FunctionSymbol;

public class RecordAccessor implements FunctionDef {

	private final FunctionSymbol sym;
	private final int index; 
	
	public RecordAccessor(FunctionSymbol sym, int index) {
		this.sym = sym;
		this.index = index;
	}

	@Override
	public FunctionSymbol getSymbol() {
		return sym;
	}
	
	public int getIndex() {
		return index;
	}

	@Override
	public Term evaluate(Term[] args) throws EvaluationException {
		Constructor ctor = (Constructor) args[0];
		return ctor.getArgs()[index];
	}

}
