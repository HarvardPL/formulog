package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * Formulog
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
import java.util.Arrays;
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
	public String getName() {
		return "rels::" + name;
	}

	@Override
	public void declare(PrintWriter out) {
		out.print("struct ");
		out.print(name);
		out.println(" {");
		declareArity(out);
		declareIndices(out);
		declareContextStruct(out);
		declareCreateContext(out);
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

	private void declareArity(PrintWriter out) {
		out.println("  enum { arity = " + arity + " };");
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

	private void declareContextStruct(PrintWriter out) {
		out.println("  struct context {");
		for (int index : indexInfo.keySet()) {
			out.println("    " + mkIndexType(index) + "::operation_hints " + mkHintName(index) + ";");
		}
		out.println("  };");
	}

	private void declareCreateContext(PrintWriter out) {
		out.println("  context create_context() const { return context(); }");
	}

	private String mkHintName(int index) {
		return mkIndexName(index) + "_hints";
	}

	private void declarePrint(PrintWriter out) {
		out.println("  void print(const string& name, bool sorted = true) const {");
		CppVar m = CppVar.mk(mkIndexName(masterIndex));
		CppFuncCall.mk("print_relation", CppVar.mk("name"), CppVar.mk("sorted"), m).toStmt().println(out, 2);
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
		declareContainsHint(out, idx);
		declareContainsNoHint(out, idx);
	}

	private CppExpr mkHint(int idx) {
		return CppAccess.mk(CppVar.mk("h"), mkHintName(idx));
	}

	private void declareContainsHint(PrintWriter out, int idx) {
		out.println("  bool " + mkContainsName(idx) + "(const " + mkTupleType() + "& tup, context& h) const {");
		CppExpr call = CppMethodCall.mk(CppVar.mk(mkIndexName(idx)), "contains", CppVar.mk("tup"), mkHint(idx));
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	private void declareContainsNoHint(PrintWriter out, int idx) {
		String name = mkContainsName(idx);
		out.println("  bool " + name + "(const " + mkTupleType() + "& tup) const {");
		CppCtor.mk("context", "h").println(out, 2);
		CppExpr call = CppFuncCall.mk(name, CppVar.mk("tup"), CppVar.mk("h"));
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
		declareInsertHint(out);
		declareInsertNoHint(out);
	}

	private void declareInsertHint(PrintWriter out) {
		out.println("  bool insert(const " + mkTupleType() + "& tup, context& h) {");
		CppVar tup = CppVar.mk("tup");
		List<CppStmt> inserts = new ArrayList<>();
		for (int i = 0; i < indexInfo.size(); ++i) {
			if (i != masterIndex) {
				inserts.add(CppMethodCall.mk(CppVar.mk(mkIndexName(i)), "insert", tup, mkHint(i)).toStmt());
			}
		}
		inserts.add(CppReturn.mk(CppConst.mkTrue()));
		CppStmt body = CppSeq.mk(inserts);
		CppExpr guard = CppMethodCall.mk(CppVar.mk(mkIndexName(masterIndex)), "insert", tup, mkHint(masterIndex));
		CppIf.mk(guard, body, CppReturn.mk(CppConst.mkFalse())).println(out, 2);
		out.println("  }");
	}

	private void declareInsertNoHint(PrintWriter out) {
		out.println("  bool insert(const " + mkTupleType() + "& tup) {");
		CppCtor.mk("context", "h").println(out, 2);
		CppExpr call = CppFuncCall.mk("insert", CppVar.mk("tup"), CppVar.mk("h"));
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	private void declareInsertAll(PrintWriter out) {
		declareGenericInsertAll(out);
	}

	private void declareGenericInsertAll(PrintWriter out) {
		out.println("  template<typename T> void insertAll(T& other) {");
		CppCtor.mk("context", "h").println(out, 2);
		CppExpr call = CppFuncCall.mk("insert", CppVar.mk("cur"), CppVar.mk("h"));
		CppForEach.mk("cur", CppVar.mk("other"), call.toStmt()).println(out, 2);
		out.println("  }");
	}

	private void declareLookup(PrintWriter out) {
		for (Map.Entry<Integer, IndexInfo> e : indexInfo.entrySet()) {
			BindingType[] pat = e.getValue().getPattern();
			int idx = e.getKey();
			declareLookupHint(out, idx, pat);
			declareLookupNoHint(out, idx, pat);
		}
	}

	private void declareLookupHint(PrintWriter out, int idx, BindingType[] pat) {
		out.print("  souffle::range<" + mkIndexType(idx) + "::iterator> ");
		out.println(mkLookupName(idx, pat) + "(const " + mkTupleType() + "& key, context& h) const {");
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
		if (emptyArgs.size() == pat.length) {
			mkLookupAll(idx).println(out, 2);
		} else {
			mkLookupSome(idx, emptyArgs).println(out, 2);
		}
		out.println("  }");
	}

	private void declareLookupNoHint(PrintWriter out, int idx, BindingType[] pat) {
		String name = mkLookupName(idx, pat);
		out.print("  souffle::range<" + mkIndexType(idx) + "::iterator> ");
		out.println(name + "(const " + mkTupleType() + "& key) const {");
		CppCtor.mk("context", "h").println(out, 2);
		CppExpr call = CppFuncCall.mk(name, CppVar.mk("key"), CppVar.mk("h"));
		CppReturn.mk(call).println(out, 2);
		out.println("  }");
	}

	private CppStmt mkLookupAll(int idx) {
		CppVar index = CppVar.mk(mkIndexName(idx));
		CppExpr begin = CppMethodCall.mk(index, "begin");
		CppExpr end = CppMethodCall.mk(index, "end");
		return CppReturn.mk(CppFuncCall.mk("souffle::make_range", begin, end));
	}

	private CppStmt mkLookupSome(int idx, List<Integer> emptyArgs) {
		CppVar index = CppVar.mk(mkIndexName(idx));
		List<CppStmt> stmts = new ArrayList<>();
		stmts.add(CppCtor.mk(mkTupleType(), "lo", CppVar.mk("key")));
		stmts.add(CppCtor.mk(mkTupleType(), "hi", CppVar.mk("key")));
		CppVar lo = CppVar.mk("lo");
		CppVar hi = CppVar.mk("hi");
		CppVar minTerm = CppVar.mk("min_term");
		CppVar maxTerm = CppVar.mk("max_term");
		for (int i : emptyArgs) {
			CppExpr subscript = CppConst.mkInt(i);
			stmts.add(CppBinop.mkAssign(CppSubscript.mk(lo, subscript), minTerm).toStmt());
			stmts.add(CppBinop.mkAssign(CppSubscript.mk(hi, subscript), maxTerm).toStmt());
		}
		CppExpr getLower = CppMethodCall.mk(index, "lower_bound", lo, mkHint(idx));
		CppExpr getUpper = CppMethodCall.mk(index, "upper_bound", hi, mkHint(idx));
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

	private String mkIndexType(int index) {
		return mkIndexName(index) + "_t";
	}

	private String mkIndexName(int index) {
		return "index_" + index;
	}

	private String mkTupleType() {
		return "Tuple<" + arity + ">";
	}

	private String mkLookupName(int index, BindingType[] pat) {
		return "lookup_" + index + "_" + Util.lookupOrCreate(pats, Arrays.asList(pat), () -> patCnt.getAndIncrement());
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
			name = CodeGenUtil.mkName(sym) + s;
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
		public CppExpr mkContains(CppExpr expr, boolean useHints) {
			return mkContains(masterIndex, expr, useHints);
		}

		@Override
		public CppExpr mkContains(int idx, CppExpr expr, boolean useHints) {
			List<CppExpr> args = new ArrayList<>();
			args.add(expr);
			if (useHints) {
				args.add(CppVar.mk(mkContextName()));
			}
			return CppMethodCall.mkThruPtr(nameVar, mkContainsName(idx), args);
		}

		@Override
		public CppExpr mkInsert(CppExpr expr, boolean useHints) {
			List<CppExpr> args = new ArrayList<>();
			args.add(expr);
			if (useHints) {
				args.add(CppVar.mk(mkContextName()));
			}
			return CppMethodCall.mkThruPtr(nameVar, "insert", args);
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
			return CppMethodCall.mkThruPtr(nameVar, "print", CppConst.mkString(name)).toStmt();
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
		public CppExpr mkLookup(int idx, BindingType[] pat, CppExpr key, boolean useHints) {
			List<CppExpr> args = new ArrayList<>();
			args.add(key);
			if (useHints) {
				args.add(CppVar.mk(mkContextName()));
			}
			return CppMethodCall.mkThruPtr(nameVar, mkLookupName(idx, pat), args);
		}

		@Override
		public CppExpr mkSize() {
			return CppMethodCall.mkThruPtr(nameVar, "size");
		}

		@Override
		public RelationStruct getStruct() {
			return BTreeRelationStruct.this;
		}

		private String mkContextName() {
			return "_" + name + "_context";
		}

		@Override
		public CppStmt mkDeclContext() {
			return CppDecl.mk(mkContextName(), CppMethodCall.mkThruPtr(nameVar, "create_context"));
		}

		@Override
		public String toString() {
			return "<" + name + ">";
		}

	}

}
