package edu.harvard.seas.pl.formulog.smt;

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

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.UncheckedEvaluationException;
import java.util.Collection;
import java.util.function.Supplier;

public class PerThreadSmtManager implements SmtLibSolver {

  private final ThreadLocal<SmtLibSolver> subManager;
  private volatile Program<?, ?> prog;

  public PerThreadSmtManager(Supplier<SmtLibSolver> managerMaker) {
    subManager =
        new ThreadLocal<SmtLibSolver>() {

          @Override
          protected SmtLibSolver initialValue() {
            SmtLibSolver m = managerMaker.get();
            try {
              m.start(prog);
            } catch (EvaluationException e) {
              throw new UncheckedEvaluationException(e.getMessage());
            }
            return m;
          }
        };
  }

  @Override
  public SmtResult check(Collection<SmtLibTerm> conjuncts, boolean getModel, int timeout)
      throws EvaluationException {
    try {
      return subManager.get().check(conjuncts, getModel, timeout);
    } catch (UncheckedEvaluationException e) {
      throw new EvaluationException(e.getMessage());
    }
  }

  @Override
  public void start(Program<?, ?> prog) throws EvaluationException {
    this.prog = prog;
  }

  @Override
  public void destroy() {
    subManager.get().destroy();
  }
}
