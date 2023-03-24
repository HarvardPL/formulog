package edu.harvard.seas.pl.formulog.codegen.ast.cpp;

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

import edu.harvard.seas.pl.formulog.codegen.CodeGenUtil;

import java.io.PrintWriter;

public class CppDecl implements CppStmt {

	private final String type;
	private final String var;
	private final CppExpr val;

	private CppDecl(String type, String var, CppExpr val) {
		this.type = type;
		this.var = var;
		this.val = val;
	}

	public static CppDecl mk(String var, CppExpr val) {
		return new CppDecl("auto", var, val);
	}

	public static CppDecl mkRef(String var, CppExpr val) {
		return new CppDecl("auto&", var, val);
	}

	@Override
	public void println(PrintWriter out, int indent) {
		CodeGenUtil.printIndent(out, indent);
		out.print(type);
		out.print(" ");
		out.print(var);
		out.print(" = ");
		val.print(out);
		out.println(";");
	}

}
