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
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public class UninstantiatedType implements PreType {

	private final BuiltInTypeSymbolBase sym;
	private final List<ParamElt> params;
	
	public UninstantiatedType(BuiltInTypeSymbolBase sym, List<ParamElt> params) {
		this.sym = sym;
		this.params = params;
		assert sym == BuiltInTypeSymbolBase.BV || sym == BuiltInTypeSymbolBase.FP;
		for (ParamElt param : params) {
			if (!(param instanceof ParamVar || param instanceof NatParam)) {
				throw new IllegalArgumentException("Cannot parameterize type " + sym + " with parameter " + param);
			}
		}
	}
	
	public UninstantiatedType(BuiltInTypeSymbolBase sym, ParamElt... params) {
		this(sym, Arrays.asList(params));
	}

	@Override
	public PreType applySubst(Map<ParamVar, ParamElt> subst) {
		List<ParamElt> newParams = new ArrayList<>();
		for (ParamElt p : params) {
			newParams.add(p.applySubst(subst));
		}
		return new UninstantiatedType(sym, newParams);
	}
	
	@Override
	public boolean containsParamVars() {
		return ParamUtil.containsParamVars(params);
	}
	
	@Override
	public Type mkFinal() {
		TypeSymbol typeSym = (TypeSymbol) GlobalSymbolManager.finalizeSymbol(sym, params);
		return AlgebraicDataType.make(typeSym);
	}
	
	@Override
	public boolean matchesParamSubKind(ParamSubKind kind) {
		switch (kind) {
		case ANY_TYPE:
			return true;
		case FUN:
		case NAT:
		case SMT_VAR:
		case SMT_VARS:
			return false;
		case PRE_SMT_TYPE:
			return ParamUtil.matchParamSubKind(params, ParamSubKind.PRE_SMT_TYPE);
		case MODEL_FREE_TYPE:
			return ParamUtil.matchParamSubKind(params, ParamSubKind.MODEL_FREE_TYPE);
		}
		throw new AssertionError("impossible");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		result = prime * result + ((sym == null) ? 0 : sym.hashCode());
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
		UninstantiatedType other = (UninstantiatedType) obj;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		if (sym == null) {
			if (other.sym != null)
				return false;
		} else if (!sym.equals(other.sym))
			return false;
		return true;
	}

}
