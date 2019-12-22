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

public enum ParamSubKind {

	NAT,
	
	ANY_TYPE,
	
	MODEL_FREE_TYPE,
	
	SMT_VAR,
	
	SMT_VARS,
	
	PRE_SMT_TYPE,
	
	FUN;
	
	public ParamKind toKind() {
		switch (this) {
		case FUN:
			return ParamKind.FUN;
		case NAT:
			return ParamKind.NAT;
		case ANY_TYPE:
		case PRE_SMT_TYPE:
		case MODEL_FREE_TYPE:
		case SMT_VAR:
		case SMT_VARS:
			return ParamKind.TYPE;
		}
		throw new AssertionError("impossible");
	}
	
}
