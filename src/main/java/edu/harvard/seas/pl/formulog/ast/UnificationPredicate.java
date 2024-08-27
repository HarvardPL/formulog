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
import java.util.Arrays;

public class UnificationPredicate implements ComplexLiteral {

  private final Term[] args;
  private final boolean negated;

  public static UnificationPredicate make(Term lhs, Term rhs, boolean negated) {
    return new UnificationPredicate(new Term[] {lhs, rhs}, negated);
  }

  private UnificationPredicate(Term[] args, boolean negated) {
    this.args = args;
    this.negated = negated;
  }

  @Override
  public Term[] getArgs() {
    return args;
  }

  public Term getLhs() {
    return args[0];
  }

  public Term getRhs() {
    return args[1];
  }

  @Override
  public UnificationPredicate applySubstitution(Substitution subst) {
    Term newLhs = getLhs().applySubstitution(subst);
    Term newRhs = getRhs().applySubstitution(subst);
    return make(newLhs, newRhs, negated);
  }

  @Override
  public boolean isNegated() {
    return negated;
  }

  @Override
  public String toString() {
    return getLhs() + (negated ? " != " : " = ") + getRhs();
  }

  @Override
  public <I, O> O accept(ComplexLiteralVisitor<I, O> visitor, I input) {
    return visitor.visit(this, input);
  }

  @Override
  public <I, O, E extends Throwable> O accept(ComplexLiteralExnVisitor<I, O, E> visitor, I input)
      throws E {
    return visitor.visit(this, input);
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + Arrays.hashCode(args);
    result = prime * result + (negated ? 1231 : 1237);
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    UnificationPredicate other = (UnificationPredicate) obj;
    if (!Arrays.equals(args, other.args)) return false;
    if (negated != other.negated) return false;
    return true;
  }
}
