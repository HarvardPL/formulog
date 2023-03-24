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

public class CppBinop implements CppExpr {

	private final CppExpr lhs;
	private final String op;
	private final CppExpr rhs;

	private CppBinop(CppExpr lhs, String op, CppExpr rhs) {
		this.lhs = lhs;
		this.op = op;
		this.rhs = rhs;
	}

	private static CppBinop mk(CppExpr lhs, String op, CppExpr rhs) {
		return new CppBinop(lhs, op, rhs);
	}

	public static CppBinop mkOrUpdate(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "|=", rhs);
	}

	public static CppBinop mkLogAnd(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "&&", rhs);
	}

	public static CppBinop mkNotEq(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "!=", rhs);
	}

	public static CppBinop mkLt(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "<", rhs);
	}

	public static CppBinop mkAssign(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "=", rhs);
	}

	public static CppExpr mkEq(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "==", rhs);
	}

	public static CppExpr mkShiftLeft(CppExpr lhs, CppExpr rhs) {
		return mk(lhs, "<<", rhs);
	}

	@Override
	public void print(PrintWriter out) {
		out.print("(");
		lhs.print(out);
		out.print(" ");
		out.print(op);
		out.print(" ");
		rhs.print(out);
		out.print(")");
	}

}
