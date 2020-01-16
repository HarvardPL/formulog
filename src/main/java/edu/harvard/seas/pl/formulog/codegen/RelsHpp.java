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

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class RelsHpp {

	private final CodeGenContext ctx;

	public RelsHpp(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public void gen(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("rels.hpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("rels.hpp").toFile())) {
			Worker pr = new Worker(out);
			CodeGenUtil.copyOver(br, out, 0);
			pr.defineRelations();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}
	}

	private class Worker {

		private final PrintWriter out;

		public Worker(PrintWriter out) {
			this.out = out;
		}

		public void defineRelations() {
			defineStructs();
			defineRelations1();
		}

		private void defineStructs() {
			for (RelationStruct struct : ctx.getRelationStructs()) {
				struct.declare(out);
				out.println();
			}
		}

		private void defineRelations1() {
			for (RelationSymbol sym : ctx.getRelationSymbols()) {
				ctx.lookupRelation(sym).mkDecl().println(out, 0);
			}
		}

	}

}
