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
import java.util.Iterator;
import java.util.List;

import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class BTreeIndex implements CppIndex {

	private final RelationSymbol sym;
	private final CodeGenContext ctx;
	private final int idx;
	private final String name;

	public static BTreeIndex mk(RelationSymbol sym, int idx, CodeGenContext ctx) {
		return new BTreeIndex(sym, idx, ctx);
	}

	private BTreeIndex(RelationSymbol sym, int idx, CodeGenContext ctx) {
		String s = "_";
		if (sym instanceof DeltaSymbol) {
			this.sym = ((DeltaSymbol) sym).getBaseSymbol();
			s += "delta_";
		} else if (sym instanceof NewSymbol) {
			this.sym = ((NewSymbol) sym).getBaseSymbol();
			s += "new_";
		} else {
			this.sym = sym;
		}
		this.idx = idx;
		this.ctx = ctx;
		this.name = this.sym + s + idx;
	}

	@Override
	public CppStmt mkDecl() {
		return new CppStmt() {

			@Override
			public void println(PrintWriter out, int indent) {
				out.print("auto ");
				out.print(name);
				out.print(" = make_unique<souffle::btree_set<Tuple<");
				out.print(sym.getArity());
				out.print(">, Comparator<");
				List<Integer> order = ctx.getEval().getDb().getComparatorOrder(sym, idx);
				for (Iterator<Integer> it = order.iterator(); it.hasNext();) {
					out.print(it.next());
					if (it.hasNext()) {
						out.print(", ");
					}
				}
				out.println(">>>();");
			}

		};
	}

	@Override
	public CppExpr mkInsert(CppExpr expr) {
		return new CppExpr() {

			@Override
			public void print(PrintWriter out) {
				out.print(name);
				out.print("->insert(");
				expr.print(out);
				out.print(")");
			}

		};
	}

	@Override
	public CppExpr mkIsEmpty() {
		return new CppExpr() {

			@Override
			public void print(PrintWriter out) {
				out.print(name);
				out.print("->empty()");
			}

		};
	}

	@Override
	public CppExpr mkTuple(List<CppExpr> exprs) {
		assert exprs.size() == sym.getArity();
		return new CppExpr() {

			@Override
			public void print(PrintWriter out) {
				out.print("Tuple<");
				out.print(sym.getArity());
				out.print(">{");
				CodeGenUtil.printSeparated(exprs, ", ", out);
				out.print("}");
			}

		};
	}

	@Override
	public CppStmt mkPrint() {
		return new CppStmt() {

			@Override
			public void println(PrintWriter out, int indent) {
				CodeGenUtil.printIndent(out, indent);
				out.print(name);
				out.println("->printTree();");
			}

		};
	}

	@Override
	public void print(PrintWriter out) {
		out.print("*");
		out.print(name);
	}

	@Override
	public CppExpr mkPartition() {
		return new CppExpr() {

			@Override
			public void print(PrintWriter out) {
				out.print(name);
				out.print("->");
				out.print("getChunks(400)");
			}
			
		};
	}

	@Override
	public CppStmt mkClear() {
		return new CppStmt() {

			@Override
			public void println(PrintWriter out, int indent) {
				CodeGenUtil.printIndent(out, indent);
				out.print(name);
				out.print("->");
				out.println("clear();");
			}
			
		};
	}

	@Override
	public CppExpr mkTupleAccess(CppExpr tup, CppExpr idx) {
		return new CppExpr() {

			@Override
			public void print(PrintWriter out) {
				tup.print(out);
				out.print("[");
				idx.print(out);
				out.print("]");
			}
			
		};
	}
	
}
