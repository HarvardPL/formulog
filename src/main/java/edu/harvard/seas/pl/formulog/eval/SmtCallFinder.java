package edu.harvard.seas.pl.formulog.eval;

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

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.Literal;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import java.util.HashSet;
import java.util.Set;

public class SmtCallFinder {

  private final Set<FunctionSymbol> smtCallSymbols = new HashSet<>();
  private final Set<FunctionSymbol> visitedFunctions = new HashSet<>();

  public SmtCallFinder() {
    smtCallSymbols.add(BuiltInFunctionSymbol.IS_SAT);
    smtCallSymbols.add(BuiltInFunctionSymbol.IS_SAT_OPT);
    smtCallSymbols.add(BuiltInFunctionSymbol.IS_VALID);
    smtCallSymbols.add(BuiltInFunctionSymbol.GET_MODEL);
    smtCallSymbols.add(BuiltInFunctionSymbol.IS_SET_SAT);
  }

  public boolean containsSmtCall(Literal l) {
    for (Term arg : l.getArgs()) {
      if (arg.accept(tv, null)) {
        return true;
      }
    }
    return false;
  }

  private final TermVisitor<Void, Boolean> tv =
      new TermVisitor<Void, Boolean>() {

        @Override
        public Boolean visit(Var t, Void in) {
          return false;
        }

        @Override
        public Boolean visit(Constructor c, Void in) {
          for (Term arg : c.getArgs()) {
            if (arg.accept(this, in)) {
              return true;
            }
          }
          return false;
        }

        @Override
        public Boolean visit(Primitive<?> p, Void in) {
          return false;
        }

        @Override
        public Boolean visit(Expr e, Void in) {
          return e.accept(ev, in);
        }
      };

  private final ExprVisitor<Void, Boolean> ev =
      new ExprVisitor<Void, Boolean>() {

        @Override
        public Boolean visit(MatchExpr matchExpr, Void in) {
          if (matchExpr.getMatchee().accept(tv, in)) {
            return true;
          }
          for (MatchClause match : matchExpr) {
            if (match.getRhs().accept(tv, in)) {
              return true;
            }
          }
          return false;
        }

        @Override
        public Boolean visit(FunctionCall funcCall, Void in) {
          FunctionSymbol sym = funcCall.getSymbol();
          if (smtCallSymbols.contains(sym)) {
            return true;
          }
          for (Term arg : funcCall.getArgs()) {
            if (arg.accept(tv, in)) {
              return true;
            }
          }
          FunctionDef def = funcCall.getFactory().getDefManager().lookup(sym);
          if (def instanceof UserFunctionDef
              && visitedFunctions.add(sym)
              && ((UserFunctionDef) def).getBody().accept(tv, in)) {
            smtCallSymbols.add(sym);
            return true;
          }
          return false;
        }

        @Override
        public Boolean visit(LetFunExpr funcDef, Void in) {
          throw new AssertionError("impossible");
        }

        @Override
        public Boolean visit(Fold fold, Void in) {
          return fold.getShamCall().accept(this, in);
        }
      };
}
