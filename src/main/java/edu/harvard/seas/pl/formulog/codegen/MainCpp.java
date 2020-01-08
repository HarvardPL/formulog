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
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.Stratum;

public class MainCpp {

	private final CodeGenContext ctx;
	private final TermCodeGen tcg;

	public MainCpp(CodeGenContext ctx) {
		this.ctx = ctx;
		this.tcg = new TermCodeGen(ctx);
	}

	public void gen(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("main.cpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("main.cpp").toFile())) {
			Worker pr = new Worker(out);
			copyOver(br, out, 0);
			pr.defineRelations();
			copyOver(br, out, 1);
			pr.loadEdbs();
			copyOver(br, out, 2);
			pr.printStratumFuncs();
			copyOver(br, out, 3);
			pr.evaluate();
			copyOver(br, out, 4);
			pr.printResults();
			copyOver(br, out, -1);
			out.flush();
		}
	}

	private void copyOver(BufferedReader in, PrintWriter out, int stopAt) throws IOException {
		String line;
		while ((line = in.readLine()) != null && !line.equals("/* INSERT " + stopAt + " */")) {
			out.println(line);
		}
	}

	private class Worker {

		private final SortedIndexedFactDb db = ctx.getEval().getDb();
		private final PrintWriter out;

		public Worker(PrintWriter out) {
			this.out = out;
		}

		public void defineRelations() {
			for (RelationSymbol sym : db.getSymbols()) {
				for (int idx = 0; idx < db.numIndices(sym); ++idx) {
					defineRelation(sym, idx);
					if (sym.isIdbSymbol()) {
						RelationSymbol delta = new DeltaSymbol(sym);
						defineRelation(delta, idx);
						RelationSymbol new_ = new NewSymbol(sym);
						defineRelation(new_, idx);
					}
				}
			}
		}

		public void defineRelation(RelationSymbol sym, int idx) {
			CppIndex index = ctx.lookupIndex(sym, idx);
			index.mkDecl().println(out, 0);
		}

		public void loadEdbs() {
			for (RelationSymbol sym : db.getSymbols()) {
				if (sym.isEdbSymbol()) {
					for (int idx = 0; idx < db.numIndices(sym); ++idx) {
						// XXX Should probably change this so that we explicitly
						// load up only the master index, and then add the
						// master index to all the other ones.
						loadEdb(sym, idx);
					}
				}
			}
		}

		public void loadEdb(RelationSymbol sym, int idx) {
			CppIndex index = ctx.lookupIndex(sym, idx);
			for (Term[] tup : db.getAll(sym)) {
				Pair<List<CppStmt>, List<CppExpr>> p = tcg.gen(Arrays.asList(tup), Collections.emptyMap());
				assert p.fst().isEmpty();
				index.mkInsert(index.mkTuple(p.snd())).toStmt().println(out, 1);
			}
		}
		
		public void printStratumFuncs() {
			StratumCodeGen scg = new StratumCodeGen(ctx);
			List<Stratum> strata = ctx.getEval().getStrata();
			for (Iterator<Stratum> it = strata.iterator(); it.hasNext();) {
				printStratumFunc(it.next(), scg);
				if (it.hasNext()) {
					out.println();
				}	
			}
		}
		
		public void printStratumFunc(Stratum stratum, StratumCodeGen sgc) {
			out.println("void stratum_" + stratum.getRank() + "() {");
			sgc.gen(stratum).println(out, 1);
			out.println("}");
		}

		public void evaluate() {
			int n = ctx.getEval().getStrata().size();
			for (int i = 0; i < n; ++i) {
				CppFuncCall.mk("stratum_" + i, Collections.emptyList()).toStmt().println(out, 1);
			}
		}

		public void printResults() {
			for (RelationSymbol sym : db.getSymbols()) {
				out.print("  cout << \"");
				out.print(sym);
				out.println("\" << endl;");
				int idx = db.getMasterIndex(sym);
				ctx.lookupIndex(sym, idx).mkPrint().println(out, 1);
			}
		}

	}

}
