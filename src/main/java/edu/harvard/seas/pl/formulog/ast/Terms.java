package edu.harvard.seas.pl.formulog.ast;

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

import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.ExceptionalFunction;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

public final class Terms {

  private Terms() {
    throw new AssertionError();
  }

  private static final Term[] EMPTY_TERMS_ARR = new Term[0];

  public static Term[] emptyArray() {
    return EMPTY_TERMS_ARR;
  }

  public static Term[] singletonArray(Term t) {
    return new Term[] {t};
  }

  public static Term[] map(Term[] ts, Function<Term, Term> f) {
    Term[] ys = new Term[ts.length];
    for (int i = 0; i < ts.length; ++i) {
      ys[i] = f.apply(ts[i]);
    }
    return ys;
  }

  public static <E extends Exception> Term[] mapExn(Term[] ts, ExceptionalFunction<Term, Term, E> f)
      throws E {
    Term[] ys = new Term[ts.length];
    for (int i = 0; i < ts.length; ++i) {
      ys[i] = f.apply(ts[i]);
    }
    return ys;
  }

  public static Term[] normalize(Term[] ts, Substitution s) throws EvaluationException {
    Term[] newTs = new Term[ts.length];
    for (int i = 0; i < ts.length; ++i) {
      newTs[i] = ts[i].normalize(s);
    }
    return newTs;
  }

  public static boolean isGround(Term t, Set<Var> boundVars) {
    return boundVars.containsAll(t.varSet());
  }

  public static Set<Var> getNonBindingVarInstances(Term t) {
    Set<Var> vars = new HashSet<>();
    t.accept(
        new TermVisitor<Void, Void>() {

          @Override
          public Void visit(Var t, Void in) {
            return null;
          }

          @Override
          public Void visit(Constructor t, Void in) {
            for (Term arg : t.getArgs()) {
              arg.accept(this, in);
            }
            return null;
          }

          @Override
          public Void visit(Primitive<?> prim, Void in) {
            return null;
          }

          @Override
          public Void visit(Expr expr, Void in) {
            vars.addAll(expr.varSet());
            return null;
          }
        },
        null);
    return vars;
  }

  public static Set<Var> getBindingVarInstances(Term t) {
    Set<Var> vars = new HashSet<>();
    t.accept(
        new TermVisitor<Void, Void>() {

          @Override
          public Void visit(Var t, Void in) {
            vars.add(t);
            return null;
          }

          @Override
          public Void visit(Constructor t, Void in) {
            for (Term arg : t.getArgs()) {
              arg.accept(this, in);
            }
            return null;
          }

          @Override
          public Void visit(Primitive<?> prim, Void in) {
            return null;
          }

          @Override
          public Void visit(Expr expr, Void in) {
            return null;
          }
        },
        null);
    return vars;
  }

  public static interface TermVisitor<I, O> {

    O visit(Var t, I in);

    O visit(Constructor c, I in);

    O visit(Primitive<?> p, I in);

    O visit(Expr e, I in);
  }

  public static interface TermVisitorExn<I, O, E extends Throwable> {

    O visit(Var x, I in) throws E;

    O visit(Constructor c, I in) throws E;

    O visit(Primitive<?> p, I in) throws E;

    O visit(Expr e, I in) throws E;
  }

  public static final Term minTerm = new DummyTerm(Integer.MIN_VALUE);

  public static final Term maxTerm = new DummyTerm(Integer.MAX_VALUE);

  private static class DummyTerm implements Term {

    private final int id;

    public DummyTerm(int id) {
      this.id = id;
    }

    @Override
    public <I, O> O accept(TermVisitor<I, O> v, I in) {
      throw new UnsupportedOperationException();
    }

    @Override
    public <I, O, E extends Throwable> O accept(TermVisitorExn<I, O, E> v, I in) throws E {
      throw new UnsupportedOperationException();
    }

    @Override
    public boolean isGround() {
      return true;
    }

    @Override
    public boolean containsUnevaluatedTerm() {
      return false;
    }

    @Override
    public Term applySubstitution(Substitution s) {
      throw new UnsupportedOperationException();
    }

    @Override
    public Term normalize(Substitution s) throws EvaluationException {
      throw new UnsupportedOperationException();
    }

    @Override
    public void varSet(Set<Var> acc) {
      throw new UnsupportedOperationException();
    }

    @Override
    public int getId() {
      return id;
    }

    @Override
    public void updateVarCounts(Map<Var, Integer> counts) {
      throw new UnsupportedOperationException();
    }

    @Override
    public String toString() {
      return "DummyTerm(" + id + ")";
    }
  }

  public static Term makeDummyTerm(int id) {
    return new DummyTerm(id);
  }

  private static final AtomicInteger idCnt = new AtomicInteger(0);

  public static int nextId() {
    return idCnt.incrementAndGet();
  }

  @SuppressWarnings("unchecked")
  public static <T extends Term> List<T> termToTermList(Term t) {
    List<T> xs = new ArrayList<>();
    Constructor c = (Constructor) t;
    while (c.getSymbol() == BuiltInConstructorSymbol.CONS) {
      Term[] args = c.getArgs();
      xs.add((T) args[0]);
      c = (Constructor) args[1];
    }
    assert c.getSymbol() == BuiltInConstructorSymbol.NIL;
    return xs;
  }

  public static <T extends Term> Term termListToTerm(List<T> l) {
    Term acc = Constructors.nil();
    for (ListIterator<T> it = l.listIterator(l.size()); it.hasPrevious(); ) {
      acc = Constructors.cons(it.previous(), acc);
    }
    return acc;
  }
}
