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

import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralExnVisitor;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import java.util.HashSet;
import java.util.Set;

public interface ComplexLiteral extends Literal {

  Term[] getArgs();

  ComplexLiteral applySubstitution(Substitution subst);

  boolean isNegated();

  default Set<Var> varSet() {
    Set<Var> vars = new HashSet<>();
    for (Term arg : getArgs()) {
      arg.varSet(vars);
    }
    return vars;
  }

  <I, O> O accept(ComplexLiteralVisitor<I, O> visitor, I input);

  <I, O, E extends Throwable> O accept(ComplexLiteralExnVisitor<I, O, E> visitor, I input) throws E;
}
