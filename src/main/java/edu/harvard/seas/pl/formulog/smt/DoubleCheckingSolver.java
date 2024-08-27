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

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import java.util.Collection;

public class DoubleCheckingSolver implements SmtLibSolver {

  private final SmtLibSolver inner;
  private final SmtLibSolver checker = new PushPopSolver();

  public DoubleCheckingSolver(SmtLibSolver inner) {
    this.inner = inner;
  }

  @Override
  public void start(Program<?, ?> prog) throws EvaluationException {
    inner.start(prog);
    checker.start(prog);
  }

  @Override
  public SmtResult check(Collection<SmtLibTerm> formula, boolean getModel, int timeout)
      throws EvaluationException {
    SmtResult res = inner.check(formula, getModel, timeout);
    if (res.status.equals(SmtStatus.UNKNOWN)) {
      SmtResult res2 = checker.check(formula, getModel, timeout);
      if (Configuration.timeSmt) {
        Configuration.recordSmtDoubleCheck(!res2.status.equals(SmtStatus.UNKNOWN));
      }
      res = res2;
    }
    return res;
  }

  @Override
  public void destroy() {
    inner.destroy();
    checker.destroy();
  }
}
