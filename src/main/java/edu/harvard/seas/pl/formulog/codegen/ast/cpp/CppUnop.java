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

import java.io.PrintWriter;

public class CppUnop implements CppExpr {

	private final String op;
	private final CppExpr expr;

	private CppUnop(String op, CppExpr expr) {
		this.op = op;
		this.expr = expr;
	}

	private static CppUnop mk(String op, CppExpr expr) {
		return new CppUnop(op, expr);
	}

	public static CppUnop mkNot(CppExpr expr) {
		return mk("!", expr);
	}

	public static CppUnop mkPreIncr(CppExpr expr) {
		return mk("++", expr);
	}

	public static CppUnop mkDeref(CppExpr expr) {
		return mk("*", expr);
	}

	@Override
	public void print(PrintWriter out) {
		out.print("(");
		out.print(op);
		expr.print(out);
		out.print(")");
	}

}
