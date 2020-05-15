package formulog.symbols;

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

import formulog.types.FunctorType;

public abstract class AbstractWrappedRelationSymbol<R extends RelationSymbol> implements WrappedRelationSymbol<R> {

	private final R baseSymbol;
	
	public AbstractWrappedRelationSymbol(R baseSymbol) {
		this.baseSymbol = baseSymbol;
	}

	@Override
	public R getBaseSymbol() {
		return baseSymbol;
	}
	
	@Override
	public FunctorType getCompileTimeType() {
		return baseSymbol.getCompileTimeType();
	}

	@Override
	public int getArity() {
		return baseSymbol.getArity();
	}

	@Override
	public boolean isIdbSymbol() {
		return baseSymbol.isIdbSymbol();
	}

	@Override
	public boolean isBottomUp() {
		return baseSymbol.isEdbSymbol();
	}

	@Override
	public boolean isTopDown() {
		return baseSymbol.isTopDown(); 
	}
	
	@Override
	public boolean isExternal() {
		return false;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((baseSymbol == null) ? 0 : baseSymbol.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AbstractWrappedRelationSymbol<?> other = (AbstractWrappedRelationSymbol<?>) obj;
		if (baseSymbol == null) {
			if (other.baseSymbol != null)
				return false;
		} else if (!baseSymbol.equals(other.baseSymbol))
			return false;
		return true;
	}

}
