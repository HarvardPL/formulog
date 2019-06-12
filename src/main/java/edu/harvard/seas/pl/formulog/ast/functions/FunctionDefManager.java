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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;

public class FunctionDefManager {

	private final Map<Symbol, FunctionDef> memo = new HashMap<>();
	private final BuiltInFunctionDefFactory builtIns;
	
	public FunctionDefManager(SymbolManager symbolManager) {
		builtIns = new BuiltInFunctionDefFactory(symbolManager);
		for (BuiltInFunctionSymbol sym : BuiltInFunctionSymbol.values()) {
			memo.put(sym, builtIns.get(sym));
		}
	}

	public void register(FunctionDef def) {
		if (memo.put(def.getSymbol(), def) != null) {
			throw new IllegalArgumentException(
					"Cannot register multiple definitions for the same function: " + def.getSymbol());
		}
	}
	
	public FunctionDef lookup(Symbol symbol) {
		FunctionDef def = memo.get(symbol);
		if (def == null) {
			throw new IllegalArgumentException("No function defined for symbol: " + symbol);
		}
		return def;
	}
	
	public boolean hasDefinition(Symbol sym) {
		return memo.containsKey(sym);
	}
	
	public Set<Symbol> getFunctionSymbols() {
		return Collections.unmodifiableSet(memo.keySet());
	}

}
