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

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.PushPopSolver;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;

public class MainCpp extends TemplateSrcFile {

  public MainCpp(CodeGenContext ctx) {
    super("main.cpp", ctx);
  }

  public void gen(BufferedReader br, PrintWriter out) throws IOException, CodeGenException {
    Worker pr = new Worker(out);
    CodeGenUtil.copyOver(br, out, 0);
    pr.loadExternalEdbs();
    CodeGenUtil.copyOver(br, out, 1);
    pr.loadStaticFacts();
    CodeGenUtil.copyOver(br, out, 2);
    pr.printIdbsToDisk();
    CodeGenUtil.copyOver(br, out, -1);
  }

  private class Worker {

    private final PrintWriter out;

    public Worker(PrintWriter out) {
      this.out = out;
    }

    public void loadExternalEdbs() {
      for (RelationSymbol sym : ctx.getProgram().getFactSymbols()) {
        if (sym.isDisk()) {
          loadExternalEdbs(sym);
        }
      }
    }

    public void loadExternalEdbs(RelationSymbol sym) {
      String func = "loadEdbs";
      CppExpr file = CppConst.mkString(sym + ".tsv");
      CppExpr repr = CppConst.mkString(ctx.lookupRepr(sym));
      CppExpr rel = CppMethodCall.mkThruPtr(CppVar.mk("globals::program"), "getRelation", repr);
      CppExpr call = CppFuncCall.mk(func, CppVar.mk("dir"), file, rel);
      call.toStmt().println(out, 1);
    }

    public void loadStaticFacts() throws CodeGenException {
      var prog = ctx.getProgram();
      prog.getFunctionCallFactory().getDefManager().loadBuiltInFunctions(new PushPopSolver());
      for (RelationSymbol sym : prog.getFactSymbols()) {
        for (Term[] tup : prog.getFacts(sym)) {
          loadStaticFact(sym, tup);
        }
      }
    }

    public void loadStaticFact(RelationSymbol sym, Term[] tup) throws CodeGenException {
      List<CppExpr> args = new ArrayList<>();
      List<CppStmt> stmts = new ArrayList<>();
      TermCodeGen tcg = new TermCodeGen(ctx);
      for (Term t : tup) {
        try {
          t = t.normalize(new SimpleSubstitution());
        } catch (EvaluationException e) {
          throw new CodeGenException("Could not normalize term occurring in fact: " + t);
        }
        Pair<CppStmt, CppExpr> p = tcg.gen(t, Collections.emptyMap());
        stmts.add(p.fst());
        args.add(p.snd());
      }
      CppExpr rel = CppConst.mkString(ctx.lookupRepr(sym));
      stmts.add(CppFuncCall.mk("loadFact", rel, CppVectorLiteral.mk(args)).toStmt());
      CppSeq.mk(stmts).println(out, 1);
    }

    public void printIdbsToDisk() {
      for (RelationSymbol sym : ctx.getProgram().getRuleSymbols()) {
        if (sym.isDisk()) {
          out.println("    saveToDisk(\"" + ctx.lookupRepr(sym) + "\");");
        }
      }
    }
  }
}
