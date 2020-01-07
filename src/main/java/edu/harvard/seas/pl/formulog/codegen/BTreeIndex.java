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

import edu.harvard.seas.pl.formulog.eval.SemiNaiveSymbol;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveSymbolType;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class BTreeIndex implements CppIndex {

	private final RelationSymbol sym;
	private final CodeGenContext ctx;
	private final int idx;
	private final boolean isDelta;
	private final String name;

	public static BTreeIndex mk(RelationSymbol sym, int idx, CodeGenContext ctx) {
		return new BTreeIndex(sym, idx, ctx);
	}

	private BTreeIndex(RelationSymbol sym, int idx, CodeGenContext ctx) {
		if (sym instanceof SemiNaiveSymbol) {
			SemiNaiveSymbol sym2 = (SemiNaiveSymbol) sym;
			assert sym2.getSemiNaiveSymbolType().equals(SemiNaiveSymbolType.DELTA);
			isDelta = true;
			this.sym = sym2.getBaseSymbol();
		} else {
			isDelta = false;
			this.sym = sym;
		}
		this.idx = idx;
		this.ctx = ctx;
		this.name = this.sym + (isDelta ? "_delta_" : "_") + idx;
	}

	@Override
	public CppStmt mkDecl() {
		return new CppStmt() {

			@Override
			public void print(PrintWriter out, int indent) {
				out.print("souffle::btree_set<Tuple<");
				out.print(sym.getArity());
				out.print(">, Comparator<");
				List<Integer> order = ctx.getEval().getDb().getComparatorOrder(sym, idx);
				for (Iterator<Integer> it = order.iterator(); it.hasNext();) {
					out.print(it.next());
					if (it.hasNext()) {
						out.print(", ");
					}
				}
				out.print(">> ");
				out.print(name);
				out.println(";");
			}

		};
	}

	@Override
	public CppExpr mkInsert(CppExpr expr) {
		return new CppExpr() {

			@Override
			public void print(PrintWriter out) {
				out.print(name);
				out.print(".insert(");
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
				out.print(".empty();");
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
				CodeGenUtil.printSeparated(out, exprs, ", ");
				out.print("}");
			}

		};
	}

	@Override
	public CppStmt mkPrint() {
		return new CppStmt() {

			@Override
			public void print(PrintWriter out, int indent) {
				CodeGenUtil.printIndent(out, indent);
				out.print(name);
				out.println(".printTree();");
			}

		};
	}

	@Override
	public void print(PrintWriter out) {
		out.print(name);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((ctx == null) ? 0 : ctx.hashCode());
		result = prime * result + idx;
		result = prime * result + (isDelta ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((sym == null) ? 0 : sym.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BTreeIndex other = (BTreeIndex) obj;
		if (ctx == null) {
			if (other.ctx != null)
				return false;
		} else if (!ctx.equals(other.ctx))
			return false;
		if (idx != other.idx)
			return false;
		if (isDelta != other.isDelta)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (sym == null) {
			if (other.sym != null)
				return false;
		} else if (!sym.equals(other.sym))
			return false;
		return true;
	}

}
