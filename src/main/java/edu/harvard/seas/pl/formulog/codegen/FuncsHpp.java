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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;

public class FuncsHpp {

	private final CodeGenContext ctx;
	
	public FuncsHpp(CodeGenContext ctx) {
		this.ctx = ctx;
	}
	
	public void gen(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("funcs.hpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("funcs.hpp").toFile())) {
			Worker pr = new Worker(out);
			CodeGenUtil.copyOver(br, out, 0);
			pr.makeDeclarations();
			CodeGenUtil.copyOver(br, out, 1);
			pr.makeDefinitions();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}		
	}
	
	private class Worker {
		private final PrintWriter out;
		
		public Worker(PrintWriter out) {
			this.out = out;
		}
		
		private void makeDeclarations() {
			
		}
		
		private void makeDefinitions() {
			
		}
		
	}

}
