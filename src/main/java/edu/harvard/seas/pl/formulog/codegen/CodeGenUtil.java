package edu.harvard.seas.pl.formulog.codegen;

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

import java.io.BufferedReader;
import java.io.IOException;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Iterator;

import edu.harvard.seas.pl.formulog.symbols.Symbol;

public final class CodeGenUtil {

	private CodeGenUtil() {
		throw new AssertionError("impossible");
	}

	public static void printIndent(PrintWriter out, int indent) {
		for (int i = 0; i < indent; ++i) {
			out.print("  ");
		}
	}

	public static void print(Iterable<CppStmt> stmts, PrintWriter out, int indent) {
		for (CppStmt stmt : stmts) {
			stmt.println(out, indent);
		}
	}

	public static void printSeparated(Iterable<CppExpr> exprs, String sep, PrintWriter out) {
		for (Iterator<CppExpr> it = exprs.iterator(); it.hasNext();) {
			it.next().print(out);
			if (it.hasNext()) {
				out.print(sep);
			}
		}
	}

	public static CppExpr mkComplexTermLookup(CppExpr base, int offset) {
		CppExpr cast = CppCast.mkReinterpret("ComplexTerm&", CppUnop.mkDeref(base));
		CppExpr access = CppAccess.mk(cast, "val");
		return CppSubscript.mk(access, CppConst.mkInt(offset));
	}

	public static void copyOver(BufferedReader in, PrintWriter out, int stopAt) throws IOException {
		String line;
		while ((line = in.readLine()) != null && !line.equals("/* INSERT " + stopAt + " */")) {
			out.println(line);
		}
	}

	public static String mkName(Symbol sym) {
		return sym.toString().replaceAll("[^A-Za-z0-9_]", "__");
	}

	public static String toString(CppStmt stmt, int indent) {
		StringWriter sw = new StringWriter();
		stmt.println(new PrintWriter(sw), indent);
		return sw.toString();
	}

}
