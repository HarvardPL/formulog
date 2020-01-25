package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * FormuLog
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

import java.io.PrintWriter;

public class CppFor implements CppStmt {

	private final String var;
	private final CppExpr init;
	private final CppExpr guard;
	private final CppExpr update;
	private final CppStmt body;
	private final boolean parallel;
	
	private CppFor(String var, CppExpr init, CppExpr guard, CppExpr update, CppStmt body, boolean parallel) {
		this.var = var;
		this.init = init;
		this.guard = guard;
		this.update = update;
		this.body = body;
		this.parallel = parallel;
	}
	
	public static CppFor mk(String var, CppExpr init, CppExpr guard, CppExpr update, CppStmt body) {
		return new CppFor(var, init, guard, update, body, false);
	}
	
	public static CppFor mkParallel(String var, CppExpr init, CppExpr guard, CppExpr update, CppStmt body) {
		return new CppFor(var, init, guard, update, body, true);
	}

	@Override
	public void println(PrintWriter out, int indent) {
		CodeGenUtil.printIndent(out, indent);
		out.print(parallel ? "pfor" : "for");
		out.print(" (auto ");
		out.print(var);
		out.print(" = ");
		init.print(out);
		out.print("; ");
		guard.print(out);
		out.print("; ");
		update.print(out);
		out.println(") {");
		body.println(out, indent + 1);
		CodeGenUtil.printIndent(out, indent);
		out.println("}");
	}

}
