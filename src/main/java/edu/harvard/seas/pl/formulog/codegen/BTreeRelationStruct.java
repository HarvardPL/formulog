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
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class BTreeRelationStruct implements RelationStruct {

	private static AtomicInteger cnt = new AtomicInteger();

	private final int arity;
	private final int masterIndex;
	private final List<List<Integer>> comparators;
	private final String name;

	public BTreeRelationStruct(int arity, int masterIndex, List<List<Integer>> comparators) {
		this.arity = arity;
		this.masterIndex = masterIndex;
		this.comparators = comparators;
		name = "btree_relation_" + cnt.getAndIncrement() + "_t";
	}

	@Override
	public void declare(PrintWriter out) {
		out.print("struct ");
		out.print(name);
		out.println(" {");
		declareIndices(out);
		declareInsert(out);
		declareInsertAll(out);
		declareEmpty(out);
		declarePurge(out);
		declarePrint(out);
		declarePartition(out);
		out.println("};");
	}

	private void declarePrint(PrintWriter out) {
		out.println("  void print() const {");
		CppVar m = CppVar.mk(mkIndexName(masterIndex));
		CppMethodCall.mk(m, "printTree").toStmt().println(out, 2);
		out.println("  }");
	}

	private void declarePurge(PrintWriter out) {
		out.println("  void purge() {");
		for (int i = 0; i < comparators.size(); ++i) {
			CppMethodCall.mk(CppVar.mk(mkIndexName(i)), "clear").toStmt().println(out, 2);
		}
		out.println("  }");
	}

	private void declareEmpty(PrintWriter out) {
		out.println("  bool empty() const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "empty");
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	private void declareInsert(PrintWriter out) {
		out.println("  bool insert(const " + mkTupleName() + "& tup) {");
		CppVar tup = CppVar.mk("tup");
		List<CppStmt> inserts = new ArrayList<>();
		for (int i = 0; i < comparators.size(); ++i) {
			if (i != masterIndex) {
				inserts.add(CppMethodCall.mk(CppVar.mk(mkIndexName(i)), "insert", tup).toStmt());
			}
		}
		inserts.add(CppReturn.mk(CppConst.mkTrue()));
		CppStmt body = CppSeq.mk(inserts);
		CppExpr guard = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "insert", tup);
		CppIf.mk(guard, body, CppReturn.mk(CppConst.mkFalse())).println(out, 2);
		out.println("  }");
	}

	private void declareInsertAll(PrintWriter out) {
		out.println("  void insertAll(const " + name + "& other) {");
		CppVar other = CppVar.mk("other");
		for (int i = 0; i < comparators.size(); ++i) {
			String indexName = mkIndexName(i);
			CppExpr otherIndex = CppAccess.mk(other, indexName);
			CppExpr call = CppMethodCall.mk(CppVar.mk(indexName), "insertAll", otherIndex);
			call.toStmt().println(out, 2);
		}
		out.println("  }");
	}

	private void declareIndices(PrintWriter out) {
		int index = 0;
		for (List<Integer> order : comparators) {
			String type = mkIndexType(index);
			out.print("  using " + type + " = souffle::btree_set<");
			out.println(mkTupleName() + ", " + mkComparator(order) + ">;");
			out.println("  " + type + " " + mkIndexName(index) + ";");
			index++;
		}
		out.println("  using iterator = " + mkIndexType(masterIndex) + "::iterator;");
	}

	private String mkIndexType(int index) {
		return mkIndexName(index) + "_t";
	}

	private String mkIndexName(int index) {
		return "index_" + index;
	}

	private String mkTupleName() {
		return "Tuple<" + arity + ">";
	}

	private String mkComparator(List<Integer> order) {
		String s = "Comparator<";
		for (Iterator<Integer> it = order.iterator(); it.hasNext();) {
			s += it.next();
			if (it.hasNext()) {
				s += ", ";
			}
		}
		return s + ">";
	}

	private void declarePartition(PrintWriter out) {
		out.println("  vector<souffle::range<iterator>> partition() const {");
		CppVar m = CppVar.mk(mkIndexName(masterIndex));
		CppExpr call = CppMethodCall.mk(m, "getChunks", CppConst.mkInt(400));
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	@Override
	public Relation mkRelation(RelationSymbol sym) {
		return new RelationImpl(sym);
	}

	private class RelationImpl implements Relation {

		private final String name;

		public RelationImpl(RelationSymbol sym) {
			String s = "";
			if (sym instanceof DeltaSymbol) {
				sym = ((DeltaSymbol) sym).getBaseSymbol();
				s += "_delta";
			} else if (sym instanceof NewSymbol) {
				sym = ((NewSymbol) sym).getBaseSymbol();
				s += "_new";
			}
			name = "__" + sym + s;
		}

		@Override
		public void print(PrintWriter out) {
			out.print("*" + name);
		}

		@Override
		public CppStmt mkDecl() {
			return new CppStmt() {

				@Override
				public void println(PrintWriter out, int indent) {
					CodeGenUtil.printIndent(out, indent);
					out.print("auto " + name);
					out.println(" = make_unique<" + BTreeRelationStruct.this.name + ">();");
				}

			};
		}

		@Override
		public CppExpr mkInsert(CppExpr expr) {
			return CppMethodCall.mkThruPtr(CppVar.mk(name), "insert", expr);
		}

		@Override
		public CppExpr mkIsEmpty() {
			return CppMethodCall.mkThruPtr(CppVar.mk(name), "empty");
		}

		@Override
		public CppExpr mkTuple(List<CppExpr> exprs) {
			assert exprs.size() == arity;
			return new CppExpr() {

				@Override
				public void print(PrintWriter out) {
					out.print(mkTupleName());
					out.print("{");
					CodeGenUtil.printSeparated(exprs, ", ", out);
					out.print("}");
				}

			};
		}

		@Override
		public CppExpr mkTupleAccess(CppExpr tup, CppExpr idx) {
			return CppSubscript.mk(tup, idx);
		}

		@Override
		public CppStmt mkPrint() {
			return CppMethodCall.mkThruPtr(CppVar.mk(name), "print").toStmt();
		}

		@Override
		public CppExpr mkPartition() {
			return CppMethodCall.mkThruPtr(CppVar.mk(name), "partition");
		}

		@Override
		public CppStmt mkPurge() {
			return CppMethodCall.mkThruPtr(CppVar.mk(name), "purge").toStmt();
		}

	}

}
