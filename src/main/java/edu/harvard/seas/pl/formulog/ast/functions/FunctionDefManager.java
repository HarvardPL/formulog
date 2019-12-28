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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.smt.SmtManager;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;

public class FunctionDefManager {

	private final Map<FunctionSymbol, FunctionDef> memo = new HashMap<>();

	public FunctionDefManager() {
		for (BuiltInFunctionSymbol sym : BuiltInFunctionSymbol.values()) {
			memo.put(sym, new DummyFunctionDef(sym));
		}
	}
	
	public void register(FunctionDef def) {
		if (memo.put(def.getSymbol(), def) != null) {
			throw new IllegalArgumentException(
					"Cannot register multiple definitions for the same function: " + def.getSymbol());
		}
	}

	public void reregister(FunctionDef def) {
		if (memo.put(def.getSymbol(), def) == null) {
			throw new IllegalArgumentException(
					"Expected there to already be a definition for function " + def.getSymbol());
		}
	}

	public FunctionDef lookup(FunctionSymbol symbol) {
		FunctionDef def = memo.get(symbol);
		if (def == null) {
			throw new IllegalArgumentException("No function defined for symbol: " + symbol);
		}
		return def;
	}

	public boolean hasDefinition(FunctionSymbol sym) {
		return memo.containsKey(sym);
	}

	public Set<FunctionSymbol> getFunctionSymbols() {
		return Collections.unmodifiableSet(new HashSet<>(memo.keySet()));
	}

	public void loadBuiltInFunctions(SmtManager smt) {
		BuiltInFunctionDefFactory builtIns = new BuiltInFunctionDefFactory(smt);
		for (BuiltInFunctionSymbol sym : BuiltInFunctionSymbol.values()) {
			memo.put(sym, builtIns.get(sym));
		}
	}

}
