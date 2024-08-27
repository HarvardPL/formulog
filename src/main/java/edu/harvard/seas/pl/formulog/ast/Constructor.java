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
package edu.harvard.seas.pl.formulog.ast;

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public interface Constructor extends Functor<ConstructorSymbol>, SmtLibTerm {

  @Override
  default <I, O> O accept(TermVisitor<I, O> v, I in) {
    return v.visit(this, in);
  }

  @Override
  default <I, O, E extends Throwable> O accept(TermVisitorExn<I, O, E> v, I in) throws E {
    return v.visit(this, in);
  }

  @Override
  default Term applySubstitution(Substitution s) {
    if (isGround()) {
      return this;
    }
    Term[] args = getArgs();
    Term[] newArgs = new Term[args.length];
    for (int i = 0; i < args.length; ++i) {
      newArgs[i] = args[i].applySubstitution(s);
    }
    return copyWithNewArgs(newArgs);
  }

  @Override
  Term copyWithNewArgs(Term[] newArgs);

  @Override
  default Term normalize(Substitution s) throws EvaluationException {
    if (isGround() && !containsUnevaluatedTerm()) {
      return this;
    }
    Term[] args = getArgs();
    Term[] newArgs = new Term[args.length];
    for (int i = 0; i < args.length; ++i) {
      newArgs[i] = args[i].normalize(s);
    }
    return copyWithNewArgs(newArgs);
  }
}
