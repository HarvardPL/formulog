package edu.harvard.seas.pl.formulog.parsing;

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

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.TypeManager;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.util.Pair;

class ParsingContext {

	private final SymbolManager sm = new SymbolManager();
	private final FunctionDefManager fdm = new FunctionDefManager(); 
	private final FunctionCallFactory fcf = new FunctionCallFactory(fdm);
	private final Map<FunctionSymbol, Pair<AlgebraicDataType, Integer>> rl = new HashMap<>();
	private final Map<ConstructorSymbol, FunctionSymbol[]> cl = new HashMap<>();
	private final TypeManager tm = new TypeManager();
	private final Map<String, AtomicInteger> nfc = new HashMap<>();
	
	public SymbolManager symbolManager() {
		return sm;
	}
	
	public FunctionCallFactory functionCallFactory() {
		return fcf;
	}
	
	public FunctionDefManager functionDefManager() {
		return fdm;
	}
	
	public Map<FunctionSymbol, Pair<AlgebraicDataType, Integer>> recordLabels() {
		return rl;
	}
	
	public Map<ConstructorSymbol, FunctionSymbol[]> constructorLabels() {
		return cl;
	}
	
	public TypeManager typeManager() {
		return tm;
	}

	public Map<String, AtomicInteger> nestedFunctionCounters() {
		return nfc;
	}

}
