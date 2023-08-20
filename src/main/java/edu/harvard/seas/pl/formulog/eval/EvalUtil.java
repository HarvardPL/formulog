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

import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public final class EvalUtil {

  private EvalUtil() {
    throw new AssertionError("impossible");
  }

  public static RelationSymbol findDelta(IndexedRule rule) {
    for (SimpleLiteral l : rule) {
      RelationSymbol delta =
          l.accept(
              new SimpleLiteralVisitor<Void, RelationSymbol>() {

                @Override
                public RelationSymbol visit(Assignment assignment, Void input) {
                  return null;
                }

                @Override
                public RelationSymbol visit(Check check, Void input) {
                  return null;
                }

                @Override
                public RelationSymbol visit(Destructor destructor, Void input) {
                  return null;
                }

                @Override
                public RelationSymbol visit(SimplePredicate predicate, Void input) {
                  if (predicate.getSymbol() instanceof DeltaSymbol) {
                    return ((DeltaSymbol) predicate.getSymbol()).getBaseSymbol();
                  } else {
                    return null;
                  }
                }
              },
              null);
      if (delta != null) {
        return delta;
      }
    }
    return null;
  }
}
