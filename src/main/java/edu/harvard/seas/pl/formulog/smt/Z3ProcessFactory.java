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

import edu.harvard.seas.pl.formulog.util.Util;
import java.io.IOException;

public class Z3ProcessFactory implements ExternalSolverProcessFactory {

  private static Z3ProcessFactory instance;

  private Z3ProcessFactory() {
    Util.assertBinaryOnPath("z3");
  }

  public static Z3ProcessFactory get() {
    if (instance == null) {
      synchronized (Z3ProcessFactory.class) {
        if (instance == null) {
          instance = new Z3ProcessFactory();
        }
      }
    }
    return instance;
  }

  @Override
  public Process newProcess(boolean incremental) throws IOException {
    return new ProcessBuilder("z3", "-in", "-smt2").redirectErrorStream(true).start();
  }
}
