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
import java.util.Iterator;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class RelationHandler {

	private final CodeGenContext ctx;
	
	public RelationHandler(CodeGenContext ctx) {
		this.ctx = ctx;
	}
	
	public void print(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("main.cpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("main.cpp").toFile())) {
			Printer pr = new Printer(out);
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
	
	private class Printer {
		
		private final SortedIndexedFactDb db = ctx.getEval().getDb();
		private final PrintWriter out;
		
		public Printer(PrintWriter out) {
			this.out = out;
		}
		
		public void defineRelations() {
			for (RelationSymbol sym : db.getSymbols()) {
				for (int idx = 0; idx < db.numIndices(sym); ++idx) {
					printIndex(sym, idx);
				}
			}
		}
		
		private void printIndex(RelationSymbol sym, int idx) {
			String name = ctx.lookupRelationName(sym, idx);
			out.print("souffle::btree_set<Tuple<");
			out.print(sym.getArity());
			out.print(">, Comparator<");
			for (Iterator<Integer> it = db.getComparatorOrder(sym, idx).iterator(); it.hasNext();) {
				out.print(it.next());
				if (it.hasNext()) {
					out.print(", ");
				}
			}
			out.print(">> ");
			out.print(name);
			out.println(";");
		}
		
		public void loadEdbs() {
			for (RelationSymbol sym : db.getSymbols()) {
				if (sym.isEdbSymbol()) {
					loadEdb(sym);
				}
			}
		}
		
		public void loadEdb(RelationSymbol sym) {
			for (Term[] tup : db.getAll(sym)) {
				loadFact(sym, tup);
			}
		}
		
		public void loadFact(RelationSymbol sym, Term[] tup) {
			String insert = ".insert(Tuple<" + sym.getArity() + ">{";
			for (int i = 0; i < tup.length; ++i) {
				insert += tup[i].accept(visitor, null);
				if (i < tup.length - 1) {
					insert += ", ";
				}
			}
			insert += "});";
			for (int idx = 0; idx < db.numIndices(sym); ++idx) {
				out.print("  ");
				out.print(ctx.lookupRelationName(sym, idx));
				out.println(insert);
			}
		}

		public void printResults() {
			for (RelationSymbol sym : db.getSymbols()) {
				out.print("  cout << \"");
				out.print(sym);
				out.println("\" << endl;");
				int idx = db.getMasterIndex(sym);
				out.print("  ");
				out.print(ctx.lookupRelationName(sym, idx));
				out.println(".printTree();");
			}
		}
		
		private final TermVisitor<Void, String> visitor = new TermVisitor<Void, String>() {

			@Override
			public String visit(Var t, Void in) {
				throw new AssertionError("impossible");
			}

			@Override
			public String visit(Constructor c, Void in) {
				throw new UnsupportedOperationException("Not supporting complex terms yet");
			}

			@Override
			public String visit(Primitive<?> p, Void in) {
				if (p instanceof I32) {
					return "make_shared<BaseTerm<int32_t>>(Symbol::boxed_i32, " + p.getVal() + ")";
				} else if (p instanceof I64) {
					return "make_shared<BaseTerm<int64_t>>(Symbol::boxed_i64, " + p.getVal() + ")";
				} else if (p instanceof FP32) {
					return "make_shared<BaseTerm<float>>(Symbol::boxed_fp32, " + p.getVal() + ")";
				} else if (p instanceof FP64) {
					return "make_shared<BaseTerm<double>>(Symbol::boxed_fp64, " + p.getVal() + ")";
				} else if (p instanceof StringTerm) {
					return "make_shared<BaseTerm<std::string>>(Symbol::boxed_string, \"" + p.getVal() + "\")";
				}
				throw new UnsupportedOperationException("Unsupported primitive: " + p);
			}

			@Override
			public String visit(Expr e, Void in) {
				throw new AssertionError("impossible");
			}
			
		};
		
	}

}
