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

import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;

public final class Exprs {

  private Exprs() {
    throw new AssertionError("impossible");
  }

  public static interface ExprVisitor<I, O> {

    O visit(MatchExpr matchExpr, I in);

    O visit(FunctionCall funcCall, I in);

    O visit(LetFunExpr funcDefs, I in);

    O visit(Fold fold, I in);
  }

  public static interface ExprVisitorExn<I, O, E extends Throwable> {

    O visit(MatchExpr matchExpr, I in) throws E;

    O visit(FunctionCall funcCall, I in) throws E;

    O visit(LetFunExpr funcDefs, I in) throws E;

    O visit(Fold fold, I in) throws E;
  }
}
