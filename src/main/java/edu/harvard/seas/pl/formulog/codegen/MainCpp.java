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
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb.IndexInfo;
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
			CodeGenUtil.copyOver(br, out, 0);
			pr.defineRelations();
			CodeGenUtil.copyOver(br, out, 1);
			pr.loadEdbs();
			CodeGenUtil.copyOver(br, out, 2);
			pr.printStratumFuncs();
			CodeGenUtil.copyOver(br, out, 3);
			pr.evaluate();
			CodeGenUtil.copyOver(br, out, 4);
			pr.printResults();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}
	}

	private class Worker {

		private final SortedIndexedFactDb db = ctx.getEval().getDb();
		private final SortedIndexedFactDb deltaDb = ctx.getEval().getDeltaDb();
		private final PrintWriter out;

		public Worker(PrintWriter out) {
			this.out = out;
		}

		public void defineRelations() {
			defineRelations(db);
			out.println();
			defineRelations(deltaDb);
		}

		private void defineRelations(SortedIndexedFactDb db) {
			for (Iterator<RelationSymbol> it = db.getSymbols().iterator(); it.hasNext();) {
				defineRelation(db, it.next());
				if (it.hasNext()) {
					out.println();
				}
			}
		}

		private void defineRelation(SortedIndexedFactDb db, RelationSymbol sym) {
			RelationStruct struct = new BTreeRelationStruct(sym.getArity(), db.getMasterIndex(sym),
					mkIndexInfo(sym, db));
			struct.declare(out);
			if (db == deltaDb) {
				declareRelation(struct, new DeltaSymbol(sym));
				declareRelation(struct, new NewSymbol(sym));
			} else {
				declareRelation(struct, sym);
			}
		}

		private void declareRelation(RelationStruct struct, RelationSymbol sym) {
			Relation rel = struct.mkRelation(sym);
			rel.mkDecl().println(out, 0);
			ctx.registerRelation(sym, rel);
		}

		private Map<Integer, IndexInfo> mkIndexInfo(RelationSymbol sym, SortedIndexedFactDb db) {
			Map<Integer, IndexInfo> m = new HashMap<>();
			int n = db.numIndices(sym);
			for (int i = 0; i < n; ++i) {
				m.put(i, db.getIndexInfo(sym, i));
			}
			return m;
		}

		public void loadEdbs() {
			for (RelationSymbol sym : db.getSymbols()) {
				if (sym.isEdbSymbol()) {
					// XXX Should probably change this so that we explicitly
					// load up only the master index, and then add the
					// master index to all the other ones.
					loadEdb(sym);
				}
			}
		}

		public void loadEdb(RelationSymbol sym) {
			Relation rel = ctx.lookupRelation(sym);
			for (Term[] tup : db.getAll(sym)) {
				Pair<CppStmt, List<CppExpr>> p = tcg.gen(Arrays.asList(tup), Collections.emptyMap());
				p.fst().println(out, 1);
				rel.mkInsert(rel.mkTuple(p.snd())).toStmt().println(out, 1);
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
				ctx.lookupRelation(sym).mkPrint().println(out, 1);
			}
		}

	}

}
