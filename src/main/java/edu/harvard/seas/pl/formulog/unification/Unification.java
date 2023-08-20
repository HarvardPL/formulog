package edu.harvard.seas.pl.formulog.unification;

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

import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralExnVisitor;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public final class Unification {

  private Unification() {
    throw new AssertionError();
  }

  public static boolean canBindVars(
      ComplexLiteral atom, Set<Var> boundVars, Map<Var, Integer> varCounts)
      throws InvalidProgramException {
    return atom.accept(
        new ComplexLiteralExnVisitor<Void, Boolean, InvalidProgramException>() {

          @Override
          public Boolean visit(UserPredicate normalAtom, Void in) throws InvalidProgramException {
            return handleNormalAtom(normalAtom, boundVars, varCounts);
          }

          @Override
          public Boolean visit(UnificationPredicate unifyAtom, Void in)
              throws InvalidProgramException {
            return handleUnifyAtom(unifyAtom, boundVars);
          }
        },
        null);
  }

  private static boolean handleNormalAtom(
      UserPredicate atom, Set<Var> boundVars, Map<Var, Integer> varCounts) {
    if (atom.isNegated()) {
      // Allow anonymous variables in negated atoms.
      Set<Var> vars =
          atom.varSet().stream()
              .filter(v -> !Integer.valueOf(1).equals(varCounts.get(v)))
              .collect(Collectors.toSet());
      return boundVars.containsAll(vars);
    }
    Set<Var> nonFuncVars = new HashSet<>();
    Set<Var> funcVars = new HashSet<>();
    for (Term t : atom.getArgs()) {
      nonFuncVars.addAll(Terms.getBindingVarInstances(t));
      funcVars.addAll(Terms.getNonBindingVarInstances(t));
    }
    for (Var v : funcVars) {
      if (!boundVars.contains(v) && !nonFuncVars.contains(v)) {
        return false;
      }
    }
    return true;
  }

  private static boolean handleUnifyAtom(UnificationPredicate atom, Set<Var> boundVars)
      throws InvalidProgramException {
    Term t1 = atom.getLhs();
    Term t2 = atom.getRhs();
    if (atom.isNegated()) {
      return boundVars.containsAll(t1.varSet()) && boundVars.containsAll(t2.varSet());
    }
    Set<Var> maybeBoundVars = new HashSet<>(boundVars);
    while (handleUnifyAtomHelper(t1, t2, maybeBoundVars)) {}

    return maybeBoundVars.containsAll(atom.varSet());
  }

  private static boolean handleUnifyAtomHelper(Term t1, Term t2, Set<Var> boundVars)
      throws InvalidProgramException {
    boolean changed = false;
    if (Terms.isGround(t1, boundVars)) {
      changed |= boundVars.addAll(Terms.getBindingVarInstances(t2));
    }
    if (Terms.isGround(t2, boundVars)) {
      changed |= boundVars.addAll(Terms.getBindingVarInstances(t1));
    }
    if (t1 instanceof Constructor && t2 instanceof Constructor) {
      Constructor c1 = (Constructor) t1;
      Constructor c2 = (Constructor) t2;
      Symbol sym1 = c1.getSymbol();
      Symbol sym2 = c2.getSymbol();
      if (!sym1.equals(sym2)) {
        throw new InvalidProgramException(
            "Cannot unify a constructor of symbol "
                + sym1
                + " with a constructor of symbol "
                + sym2);
      }
      Term[] args1 = c1.getArgs();
      Term[] args2 = c2.getArgs();
      assert args1.length == args2.length;
      boolean changed2;
      do {
        changed2 = false;
        for (int i = 0; i < args1.length; ++i) {
          changed2 |= handleUnifyAtomHelper(args1[i], args2[i], boundVars);
          changed |= changed2;
        }
      } while (changed2);
    }
    return changed;
  }
}
