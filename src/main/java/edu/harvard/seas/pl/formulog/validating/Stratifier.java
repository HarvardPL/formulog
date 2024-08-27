/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2019-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.validating;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import org.jgrapht.Graph;
import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector;
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.traverse.TopologicalOrderIterator;

public class Stratifier {

  private final Program<UserPredicate, BasicRule> prog;

  public Stratifier(Program<UserPredicate, BasicRule> prog) {
    this.prog = prog;
  }

  public List<Stratum> stratify() throws InvalidProgramException {
    Graph<RelationSymbol, DependencyTypeWrapper> g =
        new DefaultDirectedGraph<>(DependencyTypeWrapper.class);
    for (RelationSymbol sym : prog.getRuleSymbols()) {
      DependencyFinder depends = new DependencyFinder();
      for (BasicRule r : prog.getRules(sym)) {
        for (ComplexLiteral bd : r) {
          depends.processAtom(bd);
        }
        UserPredicate hd = r.getHead();
        for (Term t : hd.getArgs()) {
          depends.processTerm(t);
        }
      }
      g.addVertex(sym);
      for (RelationSymbol bdSym : depends) {
        g.addVertex(bdSym);
        g.addEdge(bdSym, sym, new DependencyTypeWrapper(depends.getDependencyType(bdSym)));
      }
    }
    StrongConnectivityAlgorithm<RelationSymbol, DependencyTypeWrapper> k =
        new KosarajuStrongConnectivityInspector<>(g);
    Graph<Graph<RelationSymbol, DependencyTypeWrapper>, DefaultEdge> condensation =
        k.getCondensation();
    TopologicalOrderIterator<Graph<RelationSymbol, DependencyTypeWrapper>, DefaultEdge> topo =
        new TopologicalOrderIterator<>(condensation);
    List<Stratum> strata = new ArrayList<>();
    int rank = 0;
    InvalidProgramException exn = null;
    while (topo.hasNext()) {
      boolean hasRecursiveNegationOrAggregation = false;
      Graph<RelationSymbol, DependencyTypeWrapper> component = topo.next();
      Set<RelationSymbol> edbs =
          component.vertexSet().stream().filter(r -> r.isEdbSymbol()).collect(Collectors.toSet());
      if (!edbs.isEmpty()) {
        if (!component.edgeSet().isEmpty()) {
          throw new InvalidProgramException("EDB relations cannot have dependencies: " + edbs);
        }
        continue;
      }
      for (DependencyTypeWrapper dw : component.edgeSet()) {
        DependencyType d = dw.get();
        if (d.equals(DependencyType.NEG_OR_AGG_IN_FUN) && exn == null) {
          exn =
              new InvalidProgramException(
                  "Not stratified: the relation "
                      + component.getEdgeSource(dw)
                      + " is treated as an aggregate expression in the definition of relation "
                      + component.getEdgeTarget(dw));
        }
        hasRecursiveNegationOrAggregation |= d.equals(DependencyType.NEG_OR_AGG_IN_REL);
      }
      strata.add(new Stratum(rank, component.vertexSet(), hasRecursiveNegationOrAggregation));
      if (Configuration.debugStratification) {
        toDot(rank, component);
      }
      rank++;
    }
    if (exn != null) {
      throw exn;
    }
    return strata;
  }

  private static void toDot(
      int stratumNumber, Graph<RelationSymbol, DependencyTypeWrapper> component) {
    try {
      Path base = Files.createDirectories(Paths.get(Configuration.debugStratificationOutDir));
      String name = "stratum_" + stratumNumber;
      File out = base.resolve(name + ".dot").toFile();
      try (PrintWriter pw = new PrintWriter(out)) {
        pw.println("digraph " + name + " {");
        for (RelationSymbol sym : component.vertexSet()) {
          pw.println("\t" + sym + ";");
        }
        for (DependencyTypeWrapper e : component.edgeSet()) {
          pw.print("\t");
          pw.print(component.getEdgeSource(e));
          pw.print(" -> ");
          pw.print(component.getEdgeTarget(e));
          pw.println(" [label=" + e + "];");
        }
        pw.println("}");
      }
    } catch (IOException e) {
      System.err.println("Error while writing stratification debug info");
    }
  }

  private class DependencyFinder implements Iterable<RelationSymbol> {

    private final Set<FunctionSymbol> visitedFunctions = new HashSet<>();
    private final Set<RelationSymbol> allDependencies = new HashSet<>();
    private final Set<RelationSymbol> negOrAggFunDependencies = new HashSet<>();
    private final Set<RelationSymbol> negOrAggRelDependencies = new HashSet<>();

    // private boolean isAggregate(Atom a) {
    // Symbol sym = a.getSymbol();
    // RelationProperties props = prog.getRelationProperties(sym);
    // return props != null && props.isAggregated();
    // }

    public void processAtom(ComplexLiteral a) {
      a.accept(
          new ComplexLiteralVisitor<Void, Void>() {

            @Override
            public Void visit(UnificationPredicate unificationPredicate, Void input) {
              processTerm(unificationPredicate.getLhs());
              processTerm(unificationPredicate.getRhs());
              return null;
            }

            @Override
            public Void visit(UserPredicate userPredicate, Void input) {
              if (userPredicate.isNegated()) {
                addNegOrAggRel(userPredicate.getSymbol());
              } else {
                addPositive(userPredicate.getSymbol());
              }
              for (Term t : userPredicate.getArgs()) {
                processTerm(t);
              }
              return null;
            }
          },
          null);
    }

    public DependencyType getDependencyType(RelationSymbol sym) {
      // Order is important here, since having a negative or aggregate
      // dependency within a function body subsumes having one in a
      // relation definition.
      if (negOrAggFunDependencies.contains(sym)) {
        return DependencyType.NEG_OR_AGG_IN_FUN;
      }
      if (negOrAggRelDependencies.contains(sym)) {
        return DependencyType.NEG_OR_AGG_IN_REL;
      }
      return DependencyType.POSITIVE;
    }

    private void addNegOrAggFun(RelationSymbol sym) {
      negOrAggFunDependencies.add(sym);
      allDependencies.add(sym);
    }

    private void addNegOrAggRel(RelationSymbol sym) {
      negOrAggRelDependencies.add(sym);
      allDependencies.add(sym);
    }

    private void addPositive(RelationSymbol sym) {
      allDependencies.add(sym);
    }

    public void processTerm(Term t) {
      t.accept(
          new TermVisitor<Void, Void>() {

            @Override
            public Void visit(Var t, Void in) {
              return null;
            }

            @Override
            public Void visit(Constructor t, Void in) {
              for (Term arg : t.getArgs()) {
                arg.accept(this, null);
              }
              return null;
            }

            @Override
            public Void visit(Primitive<?> prim, Void in) {
              return null;
            }

            @Override
            public Void visit(Expr expr, Void in) {
              processExpr(expr);
              return null;
            }
          },
          null);
    }

    private void processExpr(Expr expr) {
      expr.accept(
          new ExprVisitor<Void, Void>() {

            @Override
            public Void visit(MatchExpr matchExpr, Void in) {
              processTerm(matchExpr.getMatchee());
              for (MatchClause cl : matchExpr) {
                processTerm(cl.getLhs());
                processTerm(cl.getRhs());
              }
              return null;
            }

            @Override
            public Void visit(FunctionCall funcCall, Void in) {
              processFunctionSymbol(funcCall.getSymbol());
              for (Term arg : funcCall.getArgs()) {
                processTerm(arg);
              }
              return null;
            }

            @Override
            public Void visit(LetFunExpr funcDef, Void in) {
              throw new AssertionError("impossible");
            }

            @Override
            public Void visit(Fold fold, Void in) {
              fold.getShamCall().accept(this, in);
              return null;
            }
          },
          null);
    }

    private void processFunctionSymbol(FunctionSymbol sym) {
      if (!visitedFunctions.add(sym) || sym instanceof BuiltInFunctionSymbol) {
        return;
      }
      if (sym instanceof PredicateFunctionSymbol) {
        addNegOrAggFun(((PredicateFunctionSymbol) sym).getPredicateSymbol());
        return;
      }
      FunctionDef def1 = prog.getDef(sym);
      if (def1 instanceof UserFunctionDef) {
        UserFunctionDef def = (UserFunctionDef) def1;
        processTerm(def.getBody());
      }
    }

    @Override
    public Iterator<RelationSymbol> iterator() {
      return allDependencies.iterator();
    }
  }

  private static enum DependencyType {
    NEG_OR_AGG_IN_FUN,

    NEG_OR_AGG_IN_REL,

    POSITIVE;
  }

  // Needed because edges need to have unique objects as labels...
  private static class DependencyTypeWrapper {

    private final DependencyType d;

    public DependencyTypeWrapper(DependencyType d) {
      this.d = d;
    }

    public DependencyType get() {
      return d;
    }

    @Override
    public String toString() {
      return d.toString();
    }
  }
}
