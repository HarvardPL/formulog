package edu.harvard.seas.pl.formulog.symbols.parameterized;

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

import java.util.ArrayList;
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.util.TodoException;

public class ParameterizedTypeSymbol extends AbstractParameterizedSymbol<BuiltInTypeSymbolBase> {

	private ParameterizedTypeSymbol(BuiltInTypeSymbolBase base, List<ParamElt> args) {
		super(base, args);
	}

	public static ParameterizedTypeSymbol mk(BuiltInTypeSymbolBase base, List<ParamElt> args) {
		switch (base) {
		case BV:
			break;
		case FP:
			if (args.size() == 1 && args.get(0) instanceof NatParam) {
				args = new ArrayList<>(((NatParam) args.get(0)).expandAsFpAlias());
			}
			break;
		}
		return new ParameterizedTypeSymbol(base, args);
	}

	@Override
	public ParameterizedSymbol copyWithNewArgs(List<ParamElt> args) {
		return mk(getBase(), args);
	}

	@Override
	public Symbol mkFinal() {
		throw new TodoException();
	}
	
}
