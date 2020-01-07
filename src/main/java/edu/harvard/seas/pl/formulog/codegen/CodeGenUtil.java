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
import java.util.Iterator;

public final class CodeGenUtil {

	private CodeGenUtil() {
		throw new AssertionError("impossible");
	}

	public static void printIndent(PrintWriter out, int indent) {
		for (int i = 0; i < indent; ++i) {
			out.print("  ");
		}
	}
	
	public static void printSeparated(PrintWriter out, Iterable<CppExpr> exprs, String sep) {
		for (Iterator<CppExpr> it = exprs.iterator(); it.hasNext();) {
			it.next().print(out);
			if (it.hasNext()) {
				out.print(sep);
			}
		}
	}
	
}