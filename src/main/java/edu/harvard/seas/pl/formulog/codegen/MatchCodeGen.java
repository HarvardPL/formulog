/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2020-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
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
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.pcollections.HashPMap;
import org.pcollections.HashTreePMap;

public class MatchCodeGen {

  private final CodeGenContext ctx;
  private final TermCodeGen tcg;

  public MatchCodeGen(CodeGenContext ctx) {
    this.ctx = ctx;
    tcg = new TermCodeGen(ctx);
  }

  /**
   * Generate C++ code computing a match expression.
   *
   * @param match The match expression
   * @param env The current variable environment
   * @return A pair of the C++ code for the match expression and an expression representing the
   *     result of the match
   */
  public Pair<CppStmt, CppExpr> gen(MatchExpr match, Map<Var, CppExpr> env) {
    return new Worker(new HashMap<>(env)).go(match);
  }

  /**
   * This class actually does all the work of generating the C++ code. It has a few "globals" that
   * are available throughout the pattern-matching computation: a variable {@link #res res} to store
   * the result of the pattern matching computation, and a label {@link #end end} to jump to after
   * the pattern matching computation is complete.
   *
   * <p>It essentially generates a bunch of nested if statements; the innermost code jumps to {@link
   * #end end} after assigning to {@link #res res}. Backtracking is implemented by falling through
   * to the next case.
   */
  private class Worker {

    private final Map<Var, CppExpr> env;
    private final List<CppStmt> acc = new ArrayList<>();

    /** A variable to store the result of the pattern match in. */
    private final String res = ctx.newId("res");

    /** A label to jump to once the match expression has been computed. */
    private final String end = ctx.newId("end");

    public Worker(Map<Var, CppExpr> env) {
      this.env = env;
    }

    /**
     * Generate the C++ code for a match expression.
     *
     * @param match The match expression
     * @return A pair of the code and an expression holding the result of the match computation
     */
    public Pair<CppStmt, CppExpr> go(MatchExpr match) {
      var p = optimizeIfExpr(match);
      if (p != null) {
        return p;
      }
      acc.add(CppCtor.mk("term_ptr", res));
      p = tcg.gen(match.getMatchee(), env);
      acc.add(p.fst());
      String scrutineeVar = ctx.newId("scrutinee");
      acc.add(CppDecl.mk(scrutineeVar, p.snd()));
      CppExpr scrutinee = CppVar.mk(scrutineeVar);
      List<Pair<Term, Term>> clauses = preprocess(match.getClauses());
      PatternMatchTree tree = new PatternMatchTree(clauses);
      acc.add(processTree(scrutinee, tree));
      /* Generate some code that dies if no pattern has been matched. */
      acc.add(
          new CppStmt() {

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

    private Pair<CppStmt, CppExpr> optimizeIfExpr(MatchExpr match) {
      var scrutinee = match.getMatchee();
      if (!(scrutinee instanceof FunctionCallFactory.FunctionCall)) {
        return null;
      }
      var call = (FunctionCallFactory.FunctionCall) scrutinee;
      var sym = call.getSymbol();
      if (sym != BuiltInFunctionSymbol.BEQ && sym != BuiltInFunctionSymbol.BNEQ) {
        return null;
      }
      var clauses = match.getClauses();
      if (clauses.size() != 2) {
        return null;
      }
      if (clauses.get(0).getLhs() != BoolTerm.mkTrue()
          || clauses.get(1).getLhs() != BoolTerm.mkFalse()) {
        return null;
      }
      var args = call.getArgs();
      return optimizeIfExpr(
          sym == BuiltInFunctionSymbol.BEQ,
          args[0],
          args[1],
          clauses.get(0).getRhs(),
          clauses.get(1).getRhs());
    }

    private Pair<CppStmt, CppExpr> optimizeIfExpr(
        boolean equals, Term t1, Term t2, Term ifTrue, Term ifFalse) {
      List<CppStmt> stmts = new ArrayList<>();
      var p1 = tcg.gen(t1, env);
      var p2 = tcg.gen(t2, env);
      stmts.add(p1.fst());
      stmts.add(p2.fst());
      String res = ctx.newId("res");
      stmts.add(CppCtor.mk("term_ptr", res));
      CppExpr cond;
      if (equals) {
        cond = CppBinop.mkEq(p1.snd(), p2.snd());
      } else {
        cond = CppBinop.mkNotEq(p1.snd(), p2.snd());
      }
      p1 = tcg.gen(ifTrue, env);
      p2 = tcg.gen(ifFalse, env);
      CppExpr resVar = CppVar.mk(res);
      CppStmt trueBranch = CppSeq.mk(p1.fst(), CppBinop.mkAssign(resVar, p1.snd()).toStmt());
      CppStmt falseBranch = CppSeq.mk(p2.fst(), CppBinop.mkAssign(resVar, p2.snd()).toStmt());
      stmts.add(CppIf.mk(cond, trueBranch, falseBranch));
      return new Pair<>(CppSeq.mk(stmts), resVar);
    }

    /**
     * Preprocess a list of match clauses, i.e., (pattern => expression) pairs.
     *
     * @param clauses The match clauses
     * @return The updated (pattern => expression) pairs
     */
    private List<Pair<Term, Term>> preprocess(List<MatchClause> clauses) {
      List<Pair<Term, Term>> l = new ArrayList<>();
      Substitution s = new SimpleSubstitution();
      Set<Var> vars = new HashSet<>();
      /*
       * Rename variables in patterns, to ensure that patterns do not share variables
       * with each other.
       */
      for (MatchClause clause : clauses) {
        Pair<Term, Set<Var>> p = renameVars(clause.getLhs(), s);
        Term rhs = clause.getRhs().applySubstitution(s);
        l.add(new Pair<>(p.fst(), rhs));
        vars.addAll(p.snd());
      }
      /*
       * Declare all the variables used in patterns.
       */
      for (Var x : vars) {
        String id = ctx.newId("y");
        CppVar cppX = CppVar.mk(id);
        env.put(x, cppX);
        acc.add(CppCtor.mk("term_ptr", id));
      }
      return l;
    }

    /**
     * Rename the variables in a term.
     *
     * @param t The term
     * @param s A substitution to update with bindings from old variables to new ones
     * @return A pair of the new term and the set of variables in that term
     */
    private Pair<Term, Set<Var>> renameVars(Term t, Substitution s) {
      Set<Var> seen = new HashSet<>();
      Set<Var> newVars = new HashSet<>();
      Term newT =
          t.accept(
              new TermVisitor<Void, Term>() {

                @Override
                public Term visit(Var old, Void in) {
                  assert seen.add(old)
                      : "Cannot handle patterns with multiple uses of the same variable: " + t;
                  Var renamed = Var.fresh();
                  newVars.add(renamed);
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
              },
              null);
      return new Pair<>(newT, newVars);
    }

    /**
     * Given a C++ expression representing the scrutinee of a match expression and a
     * pattern-matching tree encoding the match expression's logic, generate C++ code implementing
     * the match expression.
     *
     * @param scrutinee The scrutinee
     * @param tree The pattern-matching tree
     * @return The generated C++ code
     */
    private CppStmt processTree(CppExpr scrutinee, PatternMatchTree tree) {
      return new TreeProcessor(scrutinee, tree).go();
    }

    /** This class is used to turn a pattern-matching tree into C++ code. */
    private class TreeProcessor {

      private final CppExpr scrutinee;
      private final PatternMatchTree tree;

      public TreeProcessor(CppExpr scrutinee, PatternMatchTree tree) {
        this.scrutinee = scrutinee;
        this.tree = tree;
      }

      /**
       * Generate the C++ code encoding the pattern-matching logic of this object's pattern-matching
       * tree.
       *
       * @return The generated C++ code
       */
      public CppStmt go() {
        return go(tree.getRoot(), HashTreePMap.empty());
      }

      /**
       * Generate the C++ code corresponding to a node in the pattern matching tree.
       *
       * @param node The node
       * @return
       */
      private CppStmt go(Node node, HashPMap<SymbolicTerm, CppExpr> symMap) {
        return node.accept(
            new NodeVisitor<Void, CppStmt>() {

              @Override
              public CppStmt visit(InternalNode node, Void in) {
                /*
                 * You're at an internal node that is associated with a symbolic term (derived
                 * from the scrutinee). Generate a C++ expression for the symbolic term, and
                 * then generate code for checking that term against each outgoing edge of that
                 * node.
                 */
                List<CppStmt> stmts = new ArrayList<>();
                SymbolicTerm symTerm = node.getSymbolicTerm();
                /* Generate the C++ expression for the symbolic term. */
                CppExpr expr;
                if (symTerm == BaseSymbolicTerm.INSTANCE) {
                  expr = scrutinee;
                } else {
                  DerivedSymbolicTerm dst = (DerivedSymbolicTerm) symTerm;
                  CppExpr base = symMap.get(dst.getBase());
                  assert base != null;
                  String id = ctx.newId("s");
                  stmts.add(CppDecl.mk(id, CodeGenUtil.mkComplexTermLookup(base, dst.getIndex())));
                  expr = CppVar.mk(id);
                }
                assert !(symMap.containsKey(symTerm));
                var newMap = symMap.plus(symTerm, expr);
                /* Handle the outgoing edges. */
                for (Pair<Edge<?>, Node> p : tree.getOutgoingEdges(node)) {
                  stmts.add(go(expr, p.fst(), p.snd(), newMap));
                }
                return CppSeq.mk(stmts);
              }

              @Override
              public CppStmt visit(Leaf node, Void in) {
                /*
                 * You've reached a leaf, so you've successfully matched the scrutinee against a
                 * pattern. Evaluate the expression on the right-hand side of that pattern,
                 * assign it to the result variable, and jump to the end label.
                 */
                Pair<CppStmt, CppExpr> p = tcg.gen(node.getTerm(), env);
                CppStmt assign = CppBinop.mkAssign(CppVar.mk(res), p.snd()).toStmt();
                CppStmt jump = CppGoto.mk(end);
                return CppSeq.mk(p.fst(), assign, jump);
              }
            },
            null);
      }

      /**
       * Given a C++ expression representing the current sub-scrutinee, generate C++ code
       * implementing the pattern-matching logic encoded by the given edge and the rest of the tree
       * it leads to.
       *
       * @param expr The sub-scrutinee
       * @param edge The edge encoding the next step of pattern-matching logic
       * @param dest The destination of the edge, which leads to subsequent pattern-matching logic
       * @return The generated C++ code
       */
      private CppStmt go(
          CppExpr expr, Edge<?> edge, Node dest, HashPMap<SymbolicTerm, CppExpr> symMap) {
        return edge.accept(
            new EdgeVisitor<Void, CppStmt>() {

              @Override
              public CppStmt visit(VarEdge e, Void in) {
                CppExpr x = env.get(e.getLabel());
                assert x instanceof CppVar;
                // Here, the enclosing `CppBlock` is necessary so that possible variable
                // initializations aren't in the outside scope, due to limitations of `goto`
                return CppBlock.mk(
                    CppSeq.mk(CppBinop.mkAssign(x, expr).toStmt(), go(dest, symMap)));
              }

              @Override
              public CppStmt visit(PrimEdge e, Void in) {
                Pair<CppStmt, CppExpr> p = tcg.gen(e.getLabel(), env);
                // Primitive edge should have no statements; otherwise, this could pollute the
                // enclosing scope and cause a compilation error, since `goto` can't jump over
                // variable initializations in C++
                assert CodeGenUtil.toString(p.fst(), 0).isEmpty();
                CppExpr rhs = p.snd();
                CppExpr guard = CppBinop.mkEq(expr, rhs);
                CppStmt body = go(dest, symMap);
                return CppIf.mk(guard, body);
              }

              @Override
              public CppStmt visit(CtorEdge e, Void in) {
                CppExpr symbol = CppVar.mk(ctx.lookupRepr(e.getLabel()));
                CppExpr guard = CppBinop.mkEq(CppAccess.mkThruPtr(expr, "sym"), symbol);
                CppStmt body = go(dest, symMap);
                return CppIf.mk(guard, body);
              }
            },
            null);
      }
    }
  }
}
