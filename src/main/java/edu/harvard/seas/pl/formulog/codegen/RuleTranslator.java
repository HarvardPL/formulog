package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SAtom;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SDestructorBody;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SExprBody;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SFunctorCall;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SInfixBinaryOpAtom;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SInt;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SLit;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SRule;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SRuleMode;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.STerm;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SVar;
import edu.harvard.seas.pl.formulog.eval.SmtCallFinder;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleRule;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class RuleTranslator {

  private final CodeGenContext ctx;
  private final QueryPlanner queryPlanner;
  private static final String checkPred = "CODEGEN_CHECK";
  private static int smtSupRelCount = 0;

  public RuleTranslator(CodeGenContext ctx, QueryPlanner queryPlanner) {
    this.ctx = ctx;
    this.queryPlanner = queryPlanner;
  }

  public Pair<List<SRule>, List<Stratum>> translate(BasicProgram prog) throws CodeGenException {
    var strats = checkStratification(prog);
    List<SRule> l = new ArrayList<>();
    Worker worker = new Worker(prog);
    for (var stratum : strats) {
      for (RelationSymbol sym : stratum.getPredicateSyms()) {
        for (BasicRule r : prog.getRules(sym)) {
          for (var sr : worker.translate(r)) {
            sr.setQueryPlan(queryPlanner.genPlan(sr, stratum));
            l.add(sr);
          }
        }
      }
    }
    l.addAll(worker.createProjectionRules());
    l.add(worker.createCheckRule());
    return new Pair<>(l, strats);
  }

  private List<Stratum> checkStratification(BasicProgram prog) throws CodeGenException {
    Stratifier stratifier = new Stratifier(prog);
    List<Stratum> strats;
    try {
      strats = stratifier.stratify();
    } catch (InvalidProgramException e) {
      throw new CodeGenException(e);
    }
    for (Stratum strat : strats) {
      if (strat.hasRecursiveNegationOrAggregation()) {
        throw new CodeGenException("Cannot handle recursive negation or aggregation: " + strat);
      }
    }
    return strats;
  }

  private class Worker {

    private final BasicProgram prog;
    private Map<Var, Integer> varCount;
    private final Set<Pair<RelationSymbol, List<Boolean>>> projections = new HashSet<>();
    private final SmtCallFinder scf = new SmtCallFinder();

    public Worker(BasicProgram prog) {
      this.prog = prog;
    }

    private List<SRule> translate(BasicRule br) throws CodeGenException {
      SimpleRule sr;
      try {
        ValidRule vr = ValidRule.make(br, (_lit, _vars) -> 1);
        sr = SimpleRule.make(vr, prog.getFunctionCallFactory());
        varCount = sr.countVariables();
      } catch (InvalidProgramException e) {
        throw new CodeGenException(e);
      }

      List<List<SLit>> bodies = new ArrayList<>();
      List<SLit> curBody = new ArrayList<>();
      List<Set<SVar>> vars = new ArrayList<>();
      Set<SVar> curVars = new HashSet<>();
      for (int i = 0; i < sr.getBodySize(); ++i) {
        var lit = sr.getBody(i);
        if (Configuration.codegenSplitOnSmt && curBody.size() > 1 && scf.containsSmtCall(lit)) {
          bodies.add(curBody);
          curBody = new ArrayList<>();
          vars.add(curVars);
          curVars = new HashSet<>(curVars);
        }
        var lits = translate(lit);
        curBody.addAll(lits);
        addVars(lits, curVars);
      }

      var head = sr.getHead();
      if (Configuration.codegenSplitOnSmt && curBody.size() > 1 && scf.containsSmtCall(head)) {
        bodies.add(curBody);
        curBody = new ArrayList<>();
        vars.add(curVars);
        curVars = new HashSet<>(curVars);
      }
      bodies.add(curBody);
      vars.add(curVars);

      List<SLit> headTrans = translate(head);
      assert headTrans.size() == 1;
      var newHead = headTrans.get(0);
      var liveVars = liveVarsByBody(newHead, bodies);

      List<SRule> rules = new ArrayList<>();
      SAtom prevSup = null;
      for (int i = 0; i < bodies.size(); ++i) {
        var body = bodies.get(i);
        if (prevSup != null) {
          body.add(0, prevSup);
        }
        if (i < bodies.size() - 1) {
          var presentVars = vars.get(i);
          var varsToKeep =
              presentVars.stream()
                  .filter(liveVars.get(i + 1)::contains)
                  .collect(Collectors.toList());
          var supAtom = newSmtSupAtom(varsToKeep);
          rules.add(new SRule(supAtom, body));
          prevSup = supAtom;
        } else {
          rules.add(new SRule(newHead, body));
        }
      }
      return rules;
    }

    void addVars(Collection<SLit> lits, Set<SVar> vars) {
      for (var lit : lits) {
        lit.varSet(vars);
      }
    }

    List<Set<SVar>> liveVarsByBody(SLit head, List<List<SLit>> bodies) {
      List<Set<SVar>> l = new ArrayList<>();
      Set<SVar> vars = head.varSet();
      l.add(vars);
      for (var it = bodies.listIterator(bodies.size()); it.hasPrevious(); ) {
        vars = new HashSet<>(vars);
        addVars(it.previous(), vars);
        l.add(vars);
      }
      Collections.reverse(l);
      return l;
    }

    private SAtom newSmtSupAtom(Collection<SVar> vars) {
      var name = "CODEGEN_SMT_SUP_" + smtSupRelCount++;
      ctx.registerCustomRelation(name, vars.size(), SRuleMode.OUTPUT);
      return new SAtom(name, new ArrayList<>(vars), false);
    }

    private List<SLit> translate(SimpleLiteral lit) {
      return lit.accept(
          new SimpleLiteralVisitor<Void, List<SLit>>() {
            @Override
            public List<SLit> visit(Assignment assignment, Void input) {
              STerm lhs = translate(assignment.getDef());
              STerm rhs = translate(assignment.getVal());
              return Collections.singletonList(new SInfixBinaryOpAtom(lhs, "=", rhs));
            }

            @Override
            public List<SLit> visit(Check check, Void input) {
              STerm lhs = translate(check.getLhs());
              STerm rhs = translate(check.getRhs());
              return Collections.singletonList(
                  new SInfixBinaryOpAtom(lhs, check.isNegated() ? "!=" : "=", rhs));
            }

            @Override
            public List<SLit> visit(Destructor destructor, Void input) {
              /*
               * A destructor of the form
               *
               * t -> c(X1, ..., Xn)
               *
               * gets translated as
               *
               * X0 = [[t]],
               *
               * @dtor_c(X0) = B, CODEGEN_CHECK(B, B2), X1 = @nth(0, X0, B2), ..., Xn = @nth(n
               * - 1, X0, B2).
               *
               * @dtor_c(...) returns 1 if the term has the symbol c and 0 otherwise.
               * CODEGEN_CHECK has a single tuple [1, 1]. It is there to make sure that the
               * destructor has been successful before nth is called.
               */
              List<SLit> l = new ArrayList<>();
              Term scrutinee = destructor.getScrutinee();
              STerm translatedScrutineeExpr = translate(scrutinee);
              Var scrutineeVar = Var.fresh();
              STerm translatedScrutineeVar = new SVar(scrutineeVar);
              l.add(new SInfixBinaryOpAtom(translatedScrutineeVar, "=", translatedScrutineeExpr));
              List<Var> args = Collections.singletonList(scrutineeVar);
              String functor = ctx.lookupOrCreateFunctorName(destructor.getSymbol());
              var dtor = new SDestructorBody(args, scrutineeVar, destructor.getSymbol());
              ctx.registerFunctorBody(functor, dtor);
              List<STerm> translatedArgs =
                  args.stream().map(Worker.this::translate).collect(Collectors.toList());
              assert translatedArgs.size() == 1 && translatedArgs.get(0) instanceof SVar;
              STerm lhs = new SFunctorCall(functor, translatedArgs);
              SVar recRef = new SVar(Var.fresh());
              l.add(new SInfixBinaryOpAtom(lhs, "=", recRef));
              SVar checkOutput = new SVar(Var.fresh());
              l.add(new SAtom(checkPred, Arrays.asList(recRef, checkOutput), false));
              int arity = destructor.getSymbol().getArity();
              Var[] bindings = destructor.getBindings();
              for (int i = 0; i < arity; ++i) {
                SFunctorCall call =
                    new SFunctorCall("nth", new SInt(i), translatedArgs.get(0), checkOutput);
                l.add(new SInfixBinaryOpAtom(translate(bindings[i]), "=", call));
              }
              return l;
            }

            @Override
            public List<SLit> visit(SimplePredicate predicate, Void input) {
              List<STerm> args =
                  Arrays.stream(predicate.getArgs())
                      .map(Worker.this::translate)
                      .collect(Collectors.toList());
              SLit lit;
              if (predicate.isNegated()) {
                lit = handleNegatedPredicate(predicate, args);
              } else {
                String symbol = ctx.lookupRepr(predicate.getSymbol());
                lit = new SAtom(symbol, args, false);
              }
              return Collections.singletonList(lit);
            }
          },
          null);
    }

    private SLit handleNegatedPredicate(SimplePredicate predicate, List<STerm> souffleArgs) {
      List<Boolean> projection = new ArrayList<>();
      int ignoredCount = 0;
      var args = predicate.getArgs();
      for (Term arg : args) {
        if (arg instanceof Var && varCount.get((Var) arg) == 1) {
          ignoredCount++;
          projection.add(false);
        } else {
          projection.add(true);
        }
      }
      RelationSymbol sym = predicate.getSymbol();
      if (ignoredCount == 0) {
        return new SAtom(ctx.lookupRepr(sym), souffleArgs, true);
      }
      projections.add(new Pair<>(predicate.getSymbol(), projection));
      List<STerm> newArgs = new ArrayList<>();
      for (int i = 0; i < souffleArgs.size(); ++i) {
        if (projection.get(i)) {
          newArgs.add(souffleArgs.get(i));
        }
      }
      return new SAtom(createProjectionSymbol(sym, projection), newArgs, true);
    }

    private String createProjectionSymbol(RelationSymbol sym, List<Boolean> projection) {
      StringBuilder sb = new StringBuilder();
      sb.append("CODEGEN_PROJECT_");
      sb.append(ctx.lookupRepr(sym));
      for (Boolean retain : projection) {
        sb.append(retain ? "1" : "0");
      }
      return sb.toString();
    }

    private SFunctorCall liftToFunctor(Term t) {
      String functor = ctx.lookupOrCreateFunctorName(t);
      List<Var> args = new ArrayList<>(t.varSet());
      ctx.registerFunctorBody(functor, new SExprBody(args, t));
      List<STerm> translatedArgs = args.stream().map(this::translate).collect(Collectors.toList());
      return new SFunctorCall(functor, translatedArgs);
    }

    private STerm translate(Term t) {
      return t.accept(
          new Terms.TermVisitor<Void, STerm>() {
            @Override
            public STerm visit(Var t, Void in) {
              return new SVar(t);
            }

            @Override
            public STerm visit(Constructor c, Void in) {
              return liftToFunctor(c);
            }

            @Override
            public STerm visit(Primitive<?> p, Void in) {
              return liftToFunctor(p);
            }

            @Override
            public STerm visit(Expr e, Void in) {
              return liftToFunctor(e);
            }
          },
          null);
    }

    List<SRule> createProjectionRules() {
      List<SRule> l = new ArrayList<>();
      for (var p : projections) {
        l.add(createProjection(p.fst(), p.snd()));
      }
      return l;
    }

    private SRule createProjection(RelationSymbol sym, List<Boolean> projection) {
      List<STerm> headArgs = new ArrayList<>();
      List<STerm> bodyArgs = new ArrayList<>();
      for (int i = 0; i < sym.getArity(); ++i) {
        STerm arg = new SVar(Var.fresh("x" + i));
        bodyArgs.add(arg);
        if (projection.get(i)) {
          headArgs.add(arg);
        }
      }
      String projSym = createProjectionSymbol(sym, projection);
      SLit head = new SAtom(projSym, headArgs, false);
      SLit bodyAtom = new SAtom(ctx.lookupRepr(sym), bodyArgs, false);
      ctx.registerCustomRelation(projSym, headArgs.size(), SRuleMode.INTERMEDIATE);
      return new SRule(head, bodyAtom);
    }

    public SRule createCheckRule() {
      ctx.registerCustomRelation(checkPred, 2, SRuleMode.INTERMEDIATE);
      SLit head = new SAtom(checkPred, Arrays.asList(new SInt(1), new SInt(1)), false);
      return new SRule(head);
    }
  }
}
