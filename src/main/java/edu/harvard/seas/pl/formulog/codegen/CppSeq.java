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
import java.util.Collections;
import java.util.List;

public class CppSeq implements CppStmt {

	private final List<CppStmt> stmts;
	
	private CppSeq(List<CppStmt> stmts) {
		this.stmts = stmts;
	}
	
	public static CppSeq mk(List<CppStmt> stmts) {
		if (stmts.isEmpty()) {
			return skip;
		}
		return new CppSeq(stmts);
	}
	
	public static CppSeq mk(CppStmt... stmts) {
		return mk(Arrays.asList(stmts));
	}
	
	public static CppSeq skip() {
		return skip;
	}
	
	private static final CppSeq skip = new CppSeq(Collections.emptyList());

	@Override
	public void println(PrintWriter out, int indent) {
		CodeGenUtil.print(stmts, out, indent);
	}

}
