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

import edu.harvard.seas.pl.formulog.types.BuiltInTypesFactory;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.util.TodoException;

public class MultiSymTypePreIndex implements TypePreIndex {
	
	public static final MultiSymTypePreIndex a = new MultiSymTypePreIndex(BuiltInTypesFactory.a);

	private final TypeVar var;
	
	public MultiSymTypePreIndex(TypeVar var) {
		this.var = var;
	}
	
	@Override
	public TypeVar getTypeVar() {
		return var;
	}
	
	@Override
	public MultiSymTypePreIndex freshen() {
		return new MultiSymTypePreIndex(var.freshen());
	}

	@Override
	public void check(Type type) throws TypeException {
		throw new TodoException();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((var == null) ? 0 : var.hashCode());
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
		MultiSymTypePreIndex other = (MultiSymTypePreIndex) obj;
		if (var == null) {
			if (other.var != null)
				return false;
		} else if (!var.equals(other.var))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "MultiSymTypePreIndex [var=" + var + "]";
	}

}
