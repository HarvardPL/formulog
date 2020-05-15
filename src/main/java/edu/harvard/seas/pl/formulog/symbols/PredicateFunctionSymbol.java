package edu.harvard.seas.pl.formulog.symbols;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
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


import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.db.BindingTypeArrayWrapper;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class PredicateFunctionSymbol implements FunctionSymbol {

	private static final Map<RelationSymbol, Map<BindingTypeArrayWrapper, PredicateFunctionSymbol>> memo = new HashMap<>();

	private static final Map<RelationSymbol, PredicateFunctionSymbol> placeholders = new HashMap<>();

	public static synchronized PredicateFunctionSymbol create(RelationSymbol predSym, BindingType[] bindings,
			SymbolManager sm) {
		Map<BindingTypeArrayWrapper, PredicateFunctionSymbol> m = Util.lookupOrCreate(memo, predSym,
				() -> new HashMap<>());
		BindingTypeArrayWrapper key = new BindingTypeArrayWrapper(bindings);
		PredicateFunctionSymbol funcSym = m.get(key);
		if (funcSym == null) {
			funcSym = createNew(predSym, bindings, sm);
			PredicateFunctionSymbol f2 = m.put(key, funcSym);
			assert f2 == null;
		}
		return funcSym;
	}

	public static synchronized PredicateFunctionSymbol createPlaceholder(RelationSymbol predSym, SymbolManager sm) {
		PredicateFunctionSymbol sym = Util.lookupOrCreate(placeholders, predSym,
				() -> new PredicateFunctionSymbol(predSym, null, predSym.getCompileTimeType()));
		sm.registerSymbol(sym);
		return sym;
	}

	private static PredicateFunctionSymbol createNew(RelationSymbol predSym, BindingType[] bindings, SymbolManager sm) {
		assert predSym.getArity() == bindings.length;
		List<Type> argTypes = new ArrayList<>();
		List<Type> retTypes = new ArrayList<>();
		FunctorType type = predSym.getCompileTimeType();
		int i = 0;
		for (Type ty : type.getArgTypes()) {
			if (bindings[i].isBound()) {
				argTypes.add(ty);
			} else if (bindings[i].isFree()) {
				retTypes.add(ty);
			}
			i++;
		}
		Type retType;
		if (retTypes.isEmpty()) {
			retType = BuiltInTypes.bool;
		} else if (retTypes.size() == 1) {
			retType = BuiltInTypes.list(retTypes.get(0));
		} else {
			TypeSymbol tupTypeSym = GlobalSymbolManager.lookupTupleTypeSymbol(retTypes.size());
			retType = BuiltInTypes.list(AlgebraicDataType.make(tupTypeSym, retTypes));
		}
		type = new FunctorType(argTypes, retType);
		PredicateFunctionSymbol funcSym = new PredicateFunctionSymbol(predSym, bindings, type);
		sm.registerSymbol(funcSym);
		return funcSym;
	}

	private final RelationSymbol predSymbol;
	private final BindingType[] bindings;
	private final FunctorType type;

	private PredicateFunctionSymbol(RelationSymbol predSymbol, BindingType[] bindings, FunctorType type) {
		this.predSymbol = predSymbol;
		this.bindings = bindings;
		this.type = type;
	}

	@Override
	public int getArity() {
		return type.getArgTypes().size();
	}

	@Override
	public FunctorType getCompileTimeType() {
		return type;
	}

	public RelationSymbol getPredicateSymbol() {
		return predSymbol;
	}

	public BindingType[] getBindings() {
		return bindings;
	}

	@Override
	public String toString() {
		String s = predSymbol.toString();
		if (bindings != null) {
			if (bindings.length > 0) {
				s += "<";
				for (int i = 0; i < bindings.length; ++i) {
					s += bindings[i];
					if (i < bindings.length - 1) {
						s += ",";
					}
				}
				s += ">";
			}
		} else {
			s += "?";
		}
		return s + "?";
	}

}
