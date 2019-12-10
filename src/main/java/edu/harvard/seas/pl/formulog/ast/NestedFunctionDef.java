package edu.harvard.seas.pl.formulog.ast;

import java.util.ArrayList;

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

import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class NestedFunctionDef {

	private final FunctionSymbol sym;
	private final List<Var> params;
	private final Term body;

	private NestedFunctionDef(FunctionSymbol sym, List<Var> params, Term body) {
		this.sym = sym;
		this.params = Collections.unmodifiableList(params);
		this.body = body;
		if (sym.getArity() != params.size()) {
			throw new IllegalArgumentException(
					"Mismatch between arity and number of given parameters in nested function definition: " + sym);
		}
	}
	
	public static NestedFunctionDef make(FunctionSymbol sym, List<Var> params, Term body) {
		return new NestedFunctionDef(sym, params, body);
	}
	
	public NestedFunctionDef applySubstitution(Substitution s) {
		Substitution s2 = new SimpleSubstitution();
		for (Var x : s.iterateKeys()) {
			if (!params.contains(x)) {
				s2.put(x, s.get(x));
			}
		}
		return make(sym, params, body.applySubstitution(s2));
	}
	
	public NestedFunctionDef freshen() {
		List<Var> newParams = new ArrayList<>();
		Substitution s = new SimpleSubstitution();
		for (Var param : params) {
			Var newParam = Var.fresh(param.toString());
			newParams.add(newParam);
			s.put(param, newParam);
		}
		return make(sym, newParams, body.applySubstitution(s));
	}
	
	public FunctionSymbol getSymbol() {
		return sym;
	}
	
	public List<Var> getParams() {
		return params;
	}
	
	public Term getBody() {
		return body;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((params == null) ? 0 : params.hashCode());
		result = prime * result + ((body == null) ? 0 : body.hashCode());
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
		NestedFunctionDef other = (NestedFunctionDef) obj;
		if (params == null) {
			if (other.params != null)
				return false;
		} else if (!params.equals(other.params))
			return false;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		return true;
	}

	@Override
	public String toString() {
		String s = "" + sym;
		if (!params.isEmpty()) {
			s += "(";
			for (int i = 0; i < params.size(); ++i) {
				s += params.get(i);
				if (i < params.size() - 1) {
					s += ", ";
				}
			}
			s += ")";
		}
		return s + " = " + body;
	}

}
