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

public class CppAccess implements CppExpr {

	private final CppExpr val;
	private final String field;
	private final boolean thruPtr;

	private CppAccess(CppExpr val, String field, boolean thruPtr) {
		this.val = val;
		this.field = field;
		this.thruPtr = thruPtr;
	}

	public static CppAccess mk(CppExpr val, String field) {
		return new CppAccess(val, field, false);
	}

	public static CppAccess mkThruPtr(CppExpr val, String field) {
		return new CppAccess(val, field, true);
	}

	@Override
	public void print(PrintWriter out) {
		val.print(out);
		out.print(thruPtr ? "->" : ".");
		out.print(field);
	}

}
