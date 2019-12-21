package edu.harvard.seas.pl.formulog.symbols.parameterized;

import java.util.Arrays;
import java.util.List;

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

	@Override
	public boolean matchesParamKind(ParamKind kind) {
		return kind.equals(ParamKind.NAT);
	}

	public List<NatParam> expandAsFpAlias() {
		switch (nat) {
		case 16:
			return Arrays.asList(new NatParam(5), new NatParam(11));
		case 32:
			return Arrays.asList(new NatParam(8), new NatParam(24));
		case 64:
			return Arrays.asList(new NatParam(11), new NatParam(53));
		case 128:
			return Arrays.asList(new NatParam(15), new NatParam(113));
		default:
			throw new IllegalArgumentException("Illegal floating point width alias: " + nat);
		}
	}

}
