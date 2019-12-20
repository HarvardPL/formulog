package edu.harvard.seas.pl.formulog.symbols.parameterized;

import java.util.Arrays;
import java.util.List;

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

public enum BuiltInTypeSymbolBase implements SymbolBase {
	
	BV("bv", ParamType.NAT),

	FP("fp", ParamType.NAT, ParamType.NAT),
	
	;
	
	private final String name;
	private final List<ParamType> paramTypes;

	private BuiltInTypeSymbolBase(String name, ParamType... params) {
		this.name = name;
		this.paramTypes = Arrays.asList(params);
	}

	@Override
	public int getArity() {
		return 0;
	}

	@Override
	public List<ParamType> getParamTypes() {
		return paramTypes;
	}

	@Override
	public String getName() {
		return name;
	}

}
