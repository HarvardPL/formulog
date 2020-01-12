package edu.harvard.seas.pl.formulog.codegen;

import java.io.PrintWriter;

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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.BaseSymbolicTerm;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.CtorEdge;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.DerivedSymbolicTerm;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.Edge;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.EdgeVisitor;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.InternalNode;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.Leaf;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.Node;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.NodeVisitor;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.PrimEdge;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.SymbolicTerm;
import edu.harvard.seas.pl.formulog.codegen.PatternMatchTree.VarEdge;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class MatchCodeGen {

	private final CodeGenContext ctx;
	private final TermCodeGen tcg;

	public MatchCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
		tcg = new TermCodeGen(ctx);
	}

	public Pair<CppStmt, CppExpr> gen(MatchExpr match, Map<Var, CppExpr> env) {
		return new Worker(new HashMap<>(env)).go(match);
	}

	private class Worker {

		private final Map<Var, CppExpr> env;
		private final List<CppStmt> acc = new ArrayList<>();
		private final String res = ctx.newId("res");
		private final String end = ctx.newId("end");

		public Worker(Map<Var, CppExpr> env) {
			this.env = env;
		}

		public Pair<CppStmt, CppExpr> go(MatchExpr match) {
			acc.add(CppCtor.mk("shared_ptr<Term>", res));
			Pair<CppStmt, CppExpr> p = tcg.gen(match.getMatchee(), env);
			acc.add(p.fst());
			CppExpr scrutinee = p.snd();
			List<Pair<Term, Term>> clauses = renameVariables(match.getClauses());
			PatternMatchTree tree = new PatternMatchTree(clauses);
			acc.add(processTree(scrutinee, tree));
			acc.add(new CppStmt() {

				@Override
				public void println(PrintWriter out, int indent) {
					CodeGenUtil.printIndent(out, indent);
					out.print("cerr << \"No matching case for term: \" << ");
					CppUnop.mkDeref(scrutinee).print(out);
					out.println(" << endl;");
					CodeGenUtil.printIndent(out, indent);
					out.println("cerr << ");
					out.println("R\"_(" + match + ")_\" << endl;");
					CppFuncCall.mk("abort").toStmt().println(out, indent);
				}

			});
			acc.add(CppLabel.mk(end));
			return new Pair<>(CppSeq.mk(acc), CppVar.mk(res));
		}

		private List<Pair<Term, Term>> renameVariables(List<MatchClause> clauses) {
			List<Pair<Term, Term>> l = new ArrayList<>();
			Substitution s = new SimpleSubstitution();
			Map<Integer, Var> vars = new HashMap<>();
			for (MatchClause clause : clauses) {
				Term pat = renameVars(clause.getLhs(), new int[] { 0 }, vars, s);
				Term rhs = clause.getRhs().applySubstitution(s);
				l.add(new Pair<>(pat, rhs));
			}
			for (Var x : vars.values()) {
				String id = ctx.newId("y");
				CppVar cppX = CppVar.mk(id);
				env.put(x, cppX);
				acc.add(CppCtor.mk("shared_ptr<Term>", id));
			}
			return l;
		}

		private Term renameVars(Term t, int[] idx, Map<Integer, Var> vars, Substitution s) {
			return t.accept(new TermVisitor<Void, Term>() {

				@Override
				public Term visit(Var old, Void in) {
					Var renamed = Util.lookupOrCreate(vars, idx[0]++, () -> Var.fresh());
					s.put(old, renamed);
					return renamed;
				}

				@Override
				public Term visit(Constructor c, Void in) {
					Term[] args = c.getArgs();
					Term[] newArgs = new Term[args.length];
					for (int i = 0; i < args.length; ++i) {
						newArgs[i] = args[i].accept(this, in);
					}
					return c.copyWithNewArgs(newArgs);
				}

				@Override
				public Term visit(Primitive<?> p, Void in) {
					return p;
				}

				@Override
				public Term visit(Expr e, Void in) {
					throw new AssertionError("impossible");
				}

			}, null);
		}

		private CppStmt processTree(CppExpr scrutinee, PatternMatchTree tree) {
			return new TreeProcessor(scrutinee, tree).go();
		}

		private class TreeProcessor {

			private final Map<SymbolicTerm, CppExpr> symMap = new HashMap<>();
			private final CppExpr scrutinee;
			private final PatternMatchTree tree;

			public TreeProcessor(CppExpr scrutinee, PatternMatchTree tree) {
				this.scrutinee = scrutinee;
				this.tree = tree;
			}

			public CppStmt go() {
				return go(tree.getRoot());
			}

			private CppStmt go(Node node) {
				return node.accept(new NodeVisitor<Void, CppStmt>() {

					@Override
					public CppStmt visit(InternalNode node, Void in) {
						List<CppStmt> stmts = new ArrayList<>();
						SymbolicTerm symTerm = node.getSymbolicTerm();
						CppExpr expr;
						if (symTerm == BaseSymbolicTerm.INSTANCE) {
							expr = scrutinee;
						} else {
							DerivedSymbolicTerm dst = (DerivedSymbolicTerm) symTerm;
							CppExpr base = symMap.get(dst.getBase());
							assert base != null;
							String id = ctx.newId("s");
							stmts.add(CppDecl.mkRef(id, CodeGenUtil.mkComplexTermLookup(base, dst.getIndex())));
							expr = CppVar.mk(id);
						}
						assert !(symMap.containsKey(symTerm));
						symMap.put(symTerm, expr);
						for (Map.Entry<Edge<?>, Node> e : tree.getOutgoingEdges(node).entrySet()) {
							stmts.add(go(expr, e.getKey(), e.getValue()));
						}
						return CppSeq.mk(stmts);
					}

					@Override
					public CppStmt visit(Leaf node, Void in) {
						Pair<CppStmt, CppExpr> p = tcg.gen(node.getTerm(), env);
						CppStmt assign = CppBinop.mkAssign(CppVar.mk(res), p.snd()).toStmt();
						CppStmt jump = CppGoto.mk(end);
						return CppSeq.mk(p.fst(), assign, jump);
					}

				}, null);
			}

			private CppStmt go(CppExpr expr, Edge<?> edge, Node dest) {
				return edge.accept(new EdgeVisitor<Void, CppStmt>() {

					@Override
					public CppStmt visit(VarEdge e, Void in) {
						CppExpr x = env.get(e.getLabel());
						assert x instanceof CppVar;
						return CppSeq.mk(CppBinop.mkAssign(x, expr).toStmt(), go(dest));
					}

					@Override
					public CppStmt visit(PrimEdge e, Void in) {
						Pair<CppStmt, CppExpr> p = tcg.gen(e.getLabel(), env);
						CppExpr lhs = CppMethodCall.mk(expr, "get");
						CppExpr rhs = CppMethodCall.mk(p.snd(), "get");
						CppExpr guard = CppUnop.mkNot(CppFuncCall.mk("Term::compare", lhs, rhs));
						CppStmt body = go(dest);
						return CppSeq.mk(p.fst(), CppIf.mk(guard, body));
					}

					@Override
					public CppStmt visit(CtorEdge e, Void in) {
						CppExpr symbol = CppVar.mk("Symbol::" + ctx.lookupRepr(e.getLabel()));
						CppExpr guard = CppBinop.mkEq(CppAccess.mkThruPtr(expr, "sym"), symbol);
						CppStmt body = go(dest);
						return CppIf.mk(guard, body);
					}

				}, null);
			}

		}

	}

}
