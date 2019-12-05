package edu.harvard.seas.pl.formulog.ast.functions;

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

import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class UserFunctionDef implements FunctionDef {

	private final FunctionSymbol sym;
	private final List<Var> params;
	private volatile Term body;

	private UserFunctionDef(FunctionSymbol sym, List<Var> params, Term body) {
		this.sym = sym;
		this.params = params;
		this.body = body;
	}

	public List<Var> getParams() {
		return params;
	}

	public Term getBody() {
		return body;
	}

	public void setBody(Expr newBody) {
		this.body = newBody;
	}

	@Override
	public FunctionSymbol getSymbol() {
		return sym;
	}

	@Override
	public Term evaluate(Term[] args) throws EvaluationException {
		Substitution s = new SimpleSubstitution();
		assert params.size() == args.length;
		int i = 0;
		for (Var param : params) {
			s.put(param, args[i]);
			i++;
		}
		try {
			return body.normalize(s);
		} catch (EvaluationException e) {
			throw new EvaluationException("Error evaluating function " + sym + ": " + e.getMessage());
		}
	}

	public static UserFunctionDef get(FunctionSymbol sym, List<Var> params, Term body) {
		return new UserFunctionDef(sym, params, body);
	}

	@Override
	public String toString() {
		return "UserFunctionDef [sym=" + sym + ", params=" + params + ", body=" + body + "]";
	}	

}
