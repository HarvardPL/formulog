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
import java.util.Arrays;
import java.util.List;

public class CppCtor implements CppStmt {

	private final String type;
	private final String var;
	private final List<CppExpr> args;
	private final boolean initializer;

	private CppCtor(String type, String var, List<CppExpr> args, boolean initializer) {
		this.type = type;
		this.var = var;
		this.args = args;
		this.initializer = initializer;
	}

	public static CppCtor mk(String type, String var, List<CppExpr> args) {
		return new CppCtor(type, var, args, false);
	}

	public static CppCtor mk(String type, String var, CppExpr... args) {
		return new CppCtor(type, var, Arrays.asList(args), false);
	}
	
	public static CppCtor mkInitializer(String type, String var, List<CppExpr> args) {
		return new CppCtor(type, var, args, true);
	}

	public static CppCtor mkInitializer(String type, String var, CppExpr... args) {
		return new CppCtor(type, var, Arrays.asList(args), true);
	}

	@Override
	public void println(PrintWriter out, int indent) {
		CodeGenUtil.printIndent(out, indent);
		out.print(type);
		out.print(" ");
		out.print(var);
		if (!args.isEmpty()) {
			out.print(initializer ? "{" : "(");
			CodeGenUtil.printSeparated(args, ", ", out);
			out.print(initializer ? "}" : ")");
		}
		out.println(";");
	}

}
