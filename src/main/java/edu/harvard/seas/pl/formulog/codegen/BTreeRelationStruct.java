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
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb.IndexInfo;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Util;

public class BTreeRelationStruct implements RelationStruct {

	private static AtomicInteger cnt = new AtomicInteger();
	private AtomicInteger patCnt = new AtomicInteger();

	private final int arity;
	private final int masterIndex;
	private final Map<Integer, IndexInfo> indexInfo;
	private final String name;
	private final Map<List<BindingType>, Integer> pats = new ConcurrentHashMap<>();

	public BTreeRelationStruct(int arity, int masterIndex, Map<Integer, IndexInfo> indexInfo) {
		this.arity = arity;
		this.masterIndex = masterIndex;
		this.indexInfo = indexInfo;
		name = "btree_relation_" + cnt.getAndIncrement() + "_t";
	}

	@Override
	public void declare(PrintWriter out) {
		out.print("struct ");
		out.print(name);
		out.println(" {");
		declareIndices(out);
		declareContains(out);
		declareInsert(out);
		declareInsertAll(out);
		declareLookup(out);
		declareEmpty(out);
		declarePurge(out);
		declarePrint(out);
		declarePartition(out);
		declareBegin(out);
		declareEnd(out);
		declareSize(out);
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
		for (int i = 0; i < indexInfo.size(); ++i) {
			CppMethodCall.mk(CppVar.mk(mkIndexName(i)), "clear").toStmt().println(out, 2);
		}
		out.println("  }");
	}

	private void declareContains(PrintWriter out) {
		for (int i = 0; i < indexInfo.size(); ++i) {
			declareContains(out, i);
		}
	}
	
	private void declareContains(PrintWriter out, int idx) {
		out.println("  bool " + mkContainsName(idx) + "(const " + mkTupleType() + "& tup) const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(idx)), "contains", CppVar.mk("tup"));
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}
	
	private void declareEmpty(PrintWriter out) {
		out.println("  bool empty() const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "empty");
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	private void declareInsert(PrintWriter out) {
		out.println("  bool insert(const " + mkTupleType() + "& tup) {");
		CppVar tup = CppVar.mk("tup");
		List<CppStmt> inserts = new ArrayList<>();
		for (int i = 0; i < indexInfo.size(); ++i) {
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
		declareGenericInsertAll(out);
		declareSpecializedInsertAll(out);
	}

	private void declareGenericInsertAll(PrintWriter out) {
		out.println("  template<typename T> void insertAll(T& other) {");
		CppExpr call = CppFuncCall.mk("insert", CppVar.mk("cur"));
		CppForEach.mk("cur", CppVar.mk("other"), call.toStmt()).println(out, 2);
		out.println("  }");
	}

	private void declareSpecializedInsertAll(PrintWriter out) {
		out.println("  void insertAll(const " + name + "& other) {");
		CppVar other = CppVar.mk("other");
		for (int i = 0; i < indexInfo.size(); ++i) {
			String indexName = mkIndexName(i);
			CppExpr otherIndex = CppAccess.mk(other, indexName);
			CppExpr call = CppMethodCall.mk(CppVar.mk(indexName), "insertAll", otherIndex);
			call.toStmt().println(out, 2);
		}
		out.println("  }");
	}

	private void declareLookup(PrintWriter out) {
		for (Map.Entry<Integer, IndexInfo> e : indexInfo.entrySet()) {
			for (List<BindingType> pat : e.getValue().getBindingPatterns()) {
				declareLookup(out, e.getKey(), pat);
			}
		}
	}

	private void declareLookup(PrintWriter out, int idx, List<BindingType> pat) {
		out.print("  souffle::range<" + mkIndexType(idx) + "::iterator> ");
		out.println(mkLookupName(idx, pat) + "(const " + mkTupleType() + "& key) const {");
		List<Integer> emptyArgs = new ArrayList<>();
		int i = 0;
		for (BindingType ty : pat) {
			switch (ty) {
			case BOUND:
				break;
			case FREE:
			case IGNORED:
				emptyArgs.add(i);
			}
			i++;
		}
		CppVar index = CppVar.mk(mkIndexName(idx));
		if (emptyArgs.size() == pat.size()) {
			mkLookupAll(index).println(out, 2);
		} else {
			mkLookupSome(index, emptyArgs).println(out, 2);
		}
		out.println("  }");
	}

	private CppStmt mkLookupAll(CppVar index) {
		CppExpr begin = CppMethodCall.mk(index, "begin");
		CppExpr end = CppMethodCall.mk(index, "end");
		return CppReturn.mk(CppFuncCall.mk("souffle::make_range", begin, end));
	}

	private CppStmt mkLookupSome(CppVar index, List<Integer> emptyArgs) {
		List<CppStmt> stmts = new ArrayList<>();
		stmts.add(CppCtor.mk(mkTupleType(), "lo", CppVar.mk("key")));
		stmts.add(CppCtor.mk(mkTupleType(), "hi", CppVar.mk("key")));
		CppVar lo = CppVar.mk("lo");
		CppVar hi = CppVar.mk("hi");
		CppVar minTerm = CppVar.mk("min_term");
		CppVar maxTerm = CppVar.mk("max_term");
		for (int i : emptyArgs) {
			CppExpr idx = CppConst.mkInt(i);
			stmts.add(CppBinop.mkAssign(CppSubscript.mk(lo, idx), minTerm).toStmt());
			stmts.add(CppBinop.mkAssign(CppSubscript.mk(hi, idx), maxTerm).toStmt());
		}
		CppExpr getLower = CppMethodCall.mk(index, "lower_bound", lo);
		CppExpr getUpper = CppMethodCall.mk(index, "upper_bound", hi);
		CppExpr call = CppFuncCall.mk("souffle::make_range", getLower, getUpper);
		stmts.add(CppReturn.mk(call));
		return CppSeq.mk(stmts);
	}

	private void declareBegin(PrintWriter out) {
		out.println("  iterator begin() const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "begin");
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}
	
	private void declareEnd(PrintWriter out) {
		out.println("  iterator end() const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "end");
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}
	
	private void declareSize(PrintWriter out) {
		out.println("  size_t size() const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "size");
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	private void declareIndices(PrintWriter out) {
		for (Map.Entry<Integer, IndexInfo> e : indexInfo.entrySet()) {
			int index = e.getKey();
			String type = mkIndexType(index);
			out.print("  using " + type + " = souffle::btree_set<");
			String cmp = mkComparator(e.getValue().getComparatorOrder());
			out.println(mkTupleType() + ", " + cmp + ">;");
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

	private String mkTupleType() {
		return "Tuple<" + arity + ">";
	}

	private String mkLookupName(int index, List<BindingType> pat) {
		return "lookup_" + index + "_" + Util.lookupOrCreate(pats, pat, () -> patCnt.getAndIncrement());
	}
	
	private String mkContainsName(int index) {
		return "contains_" + index;
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
		private final CppVar nameVar;

		public RelationImpl(RelationSymbol sym) {
			String s = "";
			if (sym instanceof DeltaSymbol) {
				sym = ((DeltaSymbol) sym).getBaseSymbol();
				s += "_delta";
			} else if (sym instanceof NewSymbol) {
				sym = ((NewSymbol) sym).getBaseSymbol();
				s += "_new";
			}
			name = sym + s;
			nameVar = CppVar.mk("rels::" + name);
		}

		@Override
		public void print(PrintWriter out) {
			nameVar.print(out);
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
		public CppExpr mkContains(CppExpr expr) {
			return CppMethodCall.mkThruPtr(nameVar, mkContainsName(masterIndex), expr);
		}
		
		@Override
		public CppExpr mkContains(int idx, CppExpr expr) {
			return CppMethodCall.mkThruPtr(nameVar, mkContainsName(idx), expr);
		}

		@Override
		public CppExpr mkInsert(CppExpr expr) {
			return CppMethodCall.mkThruPtr(nameVar, "insert", expr);
		}

		@Override
		public CppExpr mkInsertAll(CppExpr expr) {
			return CppMethodCall.mkThruPtr(nameVar, "insertAll", expr);
		}

		@Override
		public CppExpr mkIsEmpty() {
			return CppMethodCall.mkThruPtr(nameVar, "empty");
		}

		@Override
		public CppStmt mkDeclTuple(String name) {
			return CppCtor.mk(mkTupleType(), name);
		}
		
		@Override
		public CppStmt mkDeclTuple(String name, List<CppExpr> exprs) {
			return CppCtor.mkInitializer(mkTupleType(), name, exprs);
		}

		@Override
		public CppExpr mkTuple(List<CppExpr> exprs) {
			assert exprs.size() == arity;
			return new CppExpr() {

				@Override
				public void print(PrintWriter out) {
					out.print(mkTupleType());
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
			return CppMethodCall.mkThruPtr(nameVar, "print").toStmt();
		}

		@Override
		public CppExpr mkPartition() {
			return CppMethodCall.mkThruPtr(nameVar, "partition");
		}

		@Override
		public CppStmt mkPurge() {
			return CppMethodCall.mkThruPtr(nameVar, "purge").toStmt();
		}

		@Override
		public CppExpr mkLookup(int idx, List<BindingType> pat, CppExpr key) {
			return CppMethodCall.mkThruPtr(nameVar, mkLookupName(idx, pat), key);
		}

		@Override
		public CppExpr mkSize() {
			return CppMethodCall.mkThruPtr(nameVar, "size");
		}

	}

}
