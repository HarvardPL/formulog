package edu.harvard.seas.pl.formulog.types;

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


import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public class TypeManager {

	private final Map<TypeSymbol, TypeAlias> aliases = new HashMap<>();

	public void registerAlias(TypeAlias alias) {
		TypeAlias alias2 = aliases.putIfAbsent(alias.getSymbol(), alias);
		if (alias2 != null && !alias2.equals(alias)) {
			throw new IllegalArgumentException("Cannot register " + alias.getSymbol() + " as aliasing multiple types.");
		}
	}

	public Type lookup(TypeSymbol typeSym, List<Type> typeArgs) {
		if (!typeSym.isAlias()) {
			return AlgebraicDataType.make(typeSym, typeArgs);
		}
		TypeAlias alias = aliases.get(typeSym);
		if (alias == null) {
			throw new NoSuchElementException("No type associated with symbol " + typeSym);
		}
		return alias.instantiate(typeArgs);
	}

}
