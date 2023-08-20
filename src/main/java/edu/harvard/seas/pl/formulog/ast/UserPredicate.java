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

import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralExnVisitor;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import java.util.Arrays;

public class UserPredicate implements ComplexLiteral {

  private final RelationSymbol symbol;
  private final Term[] args;
  private final boolean negated;

  public static UserPredicate make(RelationSymbol symbol, Term[] args, boolean negated) {
    return new UserPredicate(symbol, args, negated);
  }

  private UserPredicate(RelationSymbol symbol, Term[] args, boolean negated) {
    this.symbol = symbol;
    this.args = args;
    this.negated = negated;
  }

  public RelationSymbol getSymbol() {
    return symbol;
  }

  @Override
  public Term[] getArgs() {
    return args;
  }

  @Override
  public boolean isNegated() {
    return negated;
  }

  @Override
  public UserPredicate applySubstitution(Substitution subst) {
    Term[] newArgs = new Term[args.length];
    for (int i = 0; i < args.length; ++i) {
      newArgs[i] = args[i].applySubstitution(subst);
    }
    return make(symbol, newArgs, negated);
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + Arrays.hashCode(args);
    result = prime * result + (negated ? 1231 : 1237);
    result = prime * result + ((symbol == null) ? 0 : symbol.hashCode());
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    UserPredicate other = (UserPredicate) obj;
    if (!Arrays.equals(args, other.args)) return false;
    if (negated != other.negated) return false;
    if (symbol == null) {
      if (other.symbol != null) return false;
    } else if (!symbol.equals(other.symbol)) return false;
    return true;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    if (negated) {
      sb.append("!");
    }
    sb.append(symbol);
    int arity = args.length;
    if (arity > 0) {
      sb.append('(');
      for (int i = 0; i < arity; ++i) {
        sb.append(args[i]);
        if (i < arity - 1) {
          sb.append(", ");
        }
      }
      sb.append(')');
    }
    return sb.toString();
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
}
