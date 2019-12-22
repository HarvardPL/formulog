package edu.harvard.seas.pl.formulog.symbols.parameterized;

import java.util.ArrayList;
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

public class ParamVar implements ParamElt {

	public static final ParamVar h = new ParamVar(ParamSubKind.NAT);
	public static final ParamVar i = new ParamVar(ParamSubKind.NAT);
	public static final ParamVar j = new ParamVar(ParamSubKind.NAT);
	public static final ParamVar k = new ParamVar(ParamSubKind.NAT);
	
	private final ParamSubKind kind;
	
	public ParamVar(ParamSubKind kind) {
		this.kind = kind;
	}

	@Override
	public boolean containsParamVars() {
		return true;
	}
	
	public ParamVar fresh() {
		return new ParamVar(kind);
	}
	
	public static List<ParamElt> fresh(List<ParamSubKind> kinds) {
		List<ParamElt> vars = new ArrayList<>();
		for (ParamSubKind kind : kinds) {
			vars.add(new ParamVar(kind));
		}
		return vars;
	}
	
	public ParamSubKind getParamSubKind() {
		return kind;
	}

	@Override
	public ParamElt applySubst(Map<ParamVar, ParamElt> subst) {
		if (subst.containsKey(this)) {
			return subst.get(this);
		}
		return this;
	}

	@Override
	public boolean matchesParamKind(ParamKind otherKind) {
		return kind.toKind().equals(otherKind);
	}
	
	@Override
	public boolean matchesParamSubKind(ParamSubKind otherKind) {
		return kind.equals(otherKind);
	}

}
