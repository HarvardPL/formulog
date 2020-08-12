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

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.util.Pair;

public class CppIf implements CppStmt {

	private final List<Pair<CppExpr, CppStmt>> cases;
	private final CppStmt elseBranch;

	private CppIf(List<Pair<CppExpr, CppStmt>> cases, CppStmt elseBranch) {
		if (cases.isEmpty()) {
			throw new IllegalArgumentException("Need to have at least one case in an if statement");
		}
		this.cases = cases;
		this.elseBranch = elseBranch;
	}

	public static CppIf mk(CppExpr guard, CppStmt thenBranch) {
		return mk(guard, thenBranch, null);
	}

	public static CppIf mk(CppExpr guard, CppStmt thenBranch, CppStmt elseBranch) {
		return new CppIf(Collections.singletonList(new Pair<>(guard, thenBranch)), elseBranch);
	}

	public static CppIf mk(List<Pair<CppExpr, CppStmt>> cases) {
		return new CppIf(new ArrayList<>(cases), null);
	}

	@Override
	public void println(PrintWriter out, int indent) {
		boolean first = true;
		for (Pair<CppExpr, CppStmt> p : cases) {
			CppExpr guard = p.fst();
			CppStmt code = p.snd();
			CodeGenUtil.printIndent(out, indent);
			if (!first) {
				out.print("} else ");
			}
			out.print("if (");
			guard.print(out);
			out.println(") {");
			code.println(out, indent + 1);
			first = false;
		}
		CodeGenUtil.printIndent(out, indent);
		if (elseBranch == null) {
			out.println("}");
			return;
		}
		out.println("} else {");
		elseBranch.println(out, indent + 1);
		CodeGenUtil.printIndent(out, indent);
		out.println("}");
	}

}
