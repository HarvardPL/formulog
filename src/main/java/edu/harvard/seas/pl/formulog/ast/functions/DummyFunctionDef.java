package edu.harvard.seas.pl.formulog.ast.functions;

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

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;

public class DummyFunctionDef implements FunctionDef {

	private final FunctionSymbol sym;
	private volatile FunctionDef def;
	
	public DummyFunctionDef(FunctionSymbol sym) {
		this.sym = sym;
	}
	
	@Override
	public FunctionSymbol getSymbol() {
		return sym;
	}

	@Override
	public Term evaluate(Term[] args) throws EvaluationException {
		if (def == null) {
			throw new EvaluationException();
		}
		return def.evaluate(args);
	}
	
	public void setDef(FunctionDef def) {
		this.def = def;
	}

	public Object getDef() {
		return def;
	}

}
