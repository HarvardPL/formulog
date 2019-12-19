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

import java.util.Map;

public class NatParam implements ParamElt {

	private final int nat;
	
	public NatParam(int nat) {
		if (nat < 0) {
			throw new IllegalArgumentException("Parameter cannot be less than zero.");
		}
		this.nat = nat;
	}

	@Override
	public ParamElt applySubst(Map<ParamVar, ParamElt> subst) {
		return this;
	}
	
	public int getNat() {
		return nat;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + nat;
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
		NatParam other = (NatParam) obj;
		if (nat != other.nat)
			return false;
		return true;
	}

}
