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
package edu.harvard.seas.pl.formulog.smt;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import java.util.Collection;
import java.util.function.Supplier;

public class NotThreadSafeQueueSmtManager implements SmtLibSolver {

  private final SmtLibSolver[] solvers;
  private int pos;
  private final Supplier<SmtLibSolver> maker;

  public NotThreadSafeQueueSmtManager(int size, Supplier<SmtLibSolver> maker) {
    if (size <= 0) {
      throw new IllegalArgumentException("Cannot have non-positive number of solvers.");
    }
    solvers = new SmtLibSolver[size];
    this.maker = maker;
  }

  @Override
  public SmtResult check(Collection<SmtLibTerm> conjuncts, boolean getModel, int timeout)
      throws EvaluationException {
    SmtLibSolver solver = solvers[pos];
    SmtResult res = solver.check(conjuncts, getModel, timeout);
    pos = (pos + 1) % solvers.length;
    return res;
  }

  @Override
  public void start(Program<?, ?> prog) throws EvaluationException {
    for (int i = 0; i < solvers.length; ++i) {
      SmtLibSolver solver = maker.get();
      solver.start(prog);
      solvers[i] = solver;
    }
  }

  @Override
  public void destroy() {
    for (SmtLibSolver solver : solvers) {
      solver.destroy();
    }
  }
}
