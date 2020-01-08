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

public class CppForEach implements CppStmt {

	private final String var;
	private final CppExpr val;
	private final CppStmt body;
	
	private CppForEach(String var, CppExpr val, CppStmt body) {
		this.var = var;
		this.val = val;
		this.body = body;
	}
	
	public static CppForEach mk(String var, CppExpr val, CppStmt body) {
		return new CppForEach(var, val, body);
	}

	@Override
	public void println(PrintWriter out, int indent) {
		CodeGenUtil.printIndent(out, indent);
		out.print("for (const auto& ");
		out.print(var);
		out.print(" : ");
		val.print(out);
		out.println(") {");
		body.println(out, indent + 1);
		CodeGenUtil.printIndent(out, indent);
		out.println("}");
	}

}
