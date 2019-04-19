package edu.harvard.seas.pl.formulog.symbols;

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

import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInPredicateSymbol implements Symbol {
	
	UNIFY("unify", 2, SymbolType.SPECIAL_REL, BuiltInTypes.a, BuiltInTypes.a),
	
	;

	private final int arity;
	private final SymbolType type;
	private final String name;
	private final List<Type> argTypes;

	private BuiltInPredicateSymbol(String name, int arity, SymbolType st, Type...argTypes) {
		this.name = name;
		this.arity = arity;
		this.type = st;
		this.argTypes = Arrays.asList(argTypes);
	}

	@Override
	public int getArity() {
		return arity;
	}

	public SymbolType getSymbolType() {
		return type;
	}

	@Override
	public String toString() {
		return name;
	}

	@Override
	public Type getCompileTimeType() {
		return new FunctorType(argTypes, BuiltInTypes.bool);
	}
	
	public static void registerAll(SymbolManager symbolManager) {
		for (BuiltInPredicateSymbol sym : BuiltInPredicateSymbol.values()) {
			symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		}
	}

}
