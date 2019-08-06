package edu.harvard.seas.pl.formulog.validating;

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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;

public class FunctionDefValidation {

	private FunctionDefValidation() {
		throw new AssertionError();
	}

	public static void validate(Program<?, ?> prog) throws InvalidProgramException {
		for (FunctionSymbol sym : prog.getFunctionSymbols()) {
			FunctionDef def = prog.getDef(sym);
			if (def instanceof UserFunctionDef) {
				try {
					validate((UserFunctionDef) def);
				} catch (InvalidProgramException e) {
					throw new InvalidProgramException("Invalid function definition: " + sym + "\n" + e.getMessage());
				}
			}
		}
	}
	
	public static void validate(UserFunctionDef def) throws InvalidProgramException {
		Set<Var> params = checkParams(def.getParams());
		Set<Var> vars = def.getBody().varSet();
		vars.removeAll(params);
		if (!vars.isEmpty()) {
			String msg = "Unbound variable(s): ";
			for (Iterator<Var> it = vars.iterator(); it.hasNext();) {
				msg += it.next();
				if (it.hasNext()) {
					msg += ", ";
				}
			}
			throw new InvalidProgramException(msg);
		}
	}
	
	private static Set<Var> checkParams(Var[] params) throws InvalidProgramException {
		Set<Var> vars = new HashSet<>();
		for (Var param : params) {
			if (!vars.add(param)) {
				throw new InvalidProgramException("Repeated parameter: " + param);
			}
		}
		return vars;
	}
	
}
