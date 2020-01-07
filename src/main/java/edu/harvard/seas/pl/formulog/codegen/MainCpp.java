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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveSymbol;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveSymbolType;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

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
			String line;
			while (!(line = br.readLine()).equals("/* INSERT 0 */")) {
				out.println(line);
			}
			pr.defineRelations();
			while (!(line = br.readLine()).equals("/* INSERT 1 */")) {
				out.println(line);
			}
			pr.loadEdbs();
			while (!(line = br.readLine()).equals("/* INSERT 2 */")) {
				out.println(line);
			}
			pr.printResults();
			while ((line = br.readLine()) != null) {
				out.println(line);
			}
			out.flush();
		}
	}
	
	private class Worker {

		private final SortedIndexedFactDb db = ctx.getEval().getDb();
		private final PrintWriter out;
		private final Map<Pair<RelationSymbol, Integer>, CppIndex> rels = new HashMap<>();

		public Worker(PrintWriter out) {
			this.out = out;
		}

		private CppIndex lookup(RelationSymbol sym, Integer idx) {
			return rels.get(new Pair<>(sym, idx));
		}
		
		public void defineRelations() {
			for (RelationSymbol sym : db.getSymbols()) {
				for (int idx = 0; idx < db.numIndices(sym); ++idx) {
					defineRelation(sym, idx);
					if (sym.isIdbSymbol()) {
						RelationSymbol delta = SemiNaiveSymbol.make(sym, SemiNaiveSymbolType.DELTA);
						defineRelation(delta, idx);
					}
				}
			}
		}
		
		public void defineRelation(RelationSymbol sym, int idx) {
			CppIndex index = BTreeIndex.mk(sym, idx, ctx);
			index.mkDecl().print(out, 0);
			rels.put(new Pair<>(sym, idx), index);
		}

		public void loadEdbs() {
			for (RelationSymbol sym : db.getSymbols()) {
				if (sym.isEdbSymbol()) {
					for (int idx = 0; idx < db.numIndices(sym); ++idx) {
						loadEdb(sym, idx);
					}
				}
			}
		}

		public void loadEdb(RelationSymbol sym, int idx) {
			CppIndex index = lookup(sym, idx);
			for (Term[] tup : db.getAll(sym)) {
				Pair<List<CppStmt>, List<CppExpr>> p = tcg.gen(Arrays.asList(tup), Collections.emptyMap());
				assert p.fst().isEmpty();
				index.mkInsert(index.mkTuple(p.snd())).toStmt().print(out, 1);
			}
		}

		public void printResults() {
			for (RelationSymbol sym : db.getSymbols()) {
				out.print("  cout << \"");
				out.print(sym);
				out.println("\" << endl;");
				int idx = db.getMasterIndex(sym);
				lookup(sym, idx).mkPrint().print(out, 1);
			}
		}

	}

}
