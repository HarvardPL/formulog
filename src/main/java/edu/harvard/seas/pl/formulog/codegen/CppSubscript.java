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

public class CppSubscript implements CppExpr {

	private final CppExpr val;
	private final CppExpr idx;
	
	private CppSubscript(CppExpr val, CppExpr idx) {
		this.val = val;
		this.idx = idx;
	}
	
	public static CppSubscript mk(CppExpr val, CppExpr idx) {
		return new CppSubscript(val, idx);
	}

	@Override
	public void print(PrintWriter out) {
		val.print(out);
		out.print("[");
		idx.print(out);
		out.print("]");
	}

}
