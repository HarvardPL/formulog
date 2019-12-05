package edu.harvard.seas.pl.formulog.ast;

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
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
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
	
	public FunctionSymbol getSymbol() {
		return sym;
	}
	
	public List<Var> getParams() {
		return params;
	}
	
	public Term getBody() {
		return body;
	}
//
//	@Override
//	public boolean isGround() {
//		return varSet().isEmpty();
//	}
//
//	@Override
//	public Term applySubstitution(Substitution s) {
//		Substitution s2 = new SimpleSubstitution();
//		for (Var x : s2.iterateKeys()) {
//			if (!params.contains(x)) {
//				s2.put(x, s.get(x));
//			}
//		}
//		return body.applySubstitution(s2);
//	}
//
//	@Override
//	public Term normalize(Substitution s) throws EvaluationException {
//		throw new UnsupportedOperationException();
//	}
//
//	@Override
//	public void varSet(Set<Var> acc) {
//		Set<Var> xs = body.varSet();
//		xs.removeAll(params);
//		acc.addAll(xs);
//	}
//
//	@Override
//	public void updateVarCounts(Map<Var, Integer> counts) {
//		throw new UnsupportedOperationException();
//	}
//
//	@Override
//	public int getId() {
//		throw new UnsupportedOperationException();
//	}
//
//	@Override
//	public <I, O> O accept(ExprVisitor<I, O> visitor, I in) {
//		return visitor.visit(this, in);
//	}
//
//	@Override
//	public <I, O, E extends Throwable> O accept(ExprVisitorExn<I, O, E> visitor, I in) throws E {
//		return visitor.visit(this, in);
//	}

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
