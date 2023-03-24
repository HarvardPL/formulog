package edu.harvard.seas.pl.formulog.db;

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

import java.util.Arrays;

import edu.harvard.seas.pl.formulog.ast.BindingType;

public class BindingTypeArrayWrapper {
	private final BindingType[] arr;

	public BindingTypeArrayWrapper(BindingType[] arr) {
		this.arr = arr;
	}

	public BindingType[] getArr() {
		return arr;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(arr);
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
		BindingTypeArrayWrapper other = (BindingTypeArrayWrapper) obj;
		if (!Arrays.equals(arr, other.arr))
			return false;
		return true;
	}

}
