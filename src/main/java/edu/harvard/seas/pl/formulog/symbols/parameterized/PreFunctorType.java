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
import java.util.Map;

public class PreFunctorType {

	private final List<PreType> argTypes;
	private final PreType retType;
	
	public PreFunctorType(List<PreType> argTypes, PreType retType) {
		this.argTypes = argTypes;
		this.retType = retType;
	}

	public List<PreType> getArgTypes() {
		return argTypes;
	}

	public PreType getRetType() {
		return retType;
	}
	
	public PreFunctorType applySubst(Map<ParamVar, ParamElt> subst) {
		List<PreType> newArgTypes = new ArrayList<>();
		for (PreType argType : argTypes) {
			newArgTypes.add(argType.applySubst(subst));
		}
		return new PreFunctorType(newArgTypes, retType.applySubst(subst));
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((argTypes == null) ? 0 : argTypes.hashCode());
		result = prime * result + ((retType == null) ? 0 : retType.hashCode());
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
		PreFunctorType other = (PreFunctorType) obj;
		if (argTypes == null) {
			if (other.argTypes != null)
				return false;
		} else if (!argTypes.equals(other.argTypes))
			return false;
		if (retType == null) {
			if (other.retType != null)
				return false;
		} else if (!retType.equals(other.retType))
			return false;
		return true;
	}
	
}
