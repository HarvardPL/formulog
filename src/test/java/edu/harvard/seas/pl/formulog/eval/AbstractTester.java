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

import static org.junit.Assert.fail;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

public abstract class AbstractTester<T extends Evaluation> implements Tester {

  @Override
  public void test(String file, List<String> inputDirs) {
    boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
    try {
      InputStream is = getClass().getClassLoader().getResourceAsStream(file);
      if (is == null) {
        throw new FileNotFoundException(file + " not found");
      }
      List<Path> dirs = new ArrayList<>();
      for (String inputDir : inputDirs) {
        URL dir = getClass().getClassLoader().getResource(inputDir);
        dirs.add(Paths.get(dir.toURI()));
      }
      BasicProgram prog = new Parser().parse(new InputStreamReader(is), dirs);
      WellTypedProgram wellTypedProg = (new TypeChecker(prog)).typeCheck();
      T eval = setup(wellTypedProg);
      boolean ok = evaluate(eval);
      if (!ok && !isBad) {
        String msg = "Test failed for a good program";
        fail(msg);
      }
      if (ok && isBad) {
        fail("Test succeeded for a bad program");
      }
    } catch (Exception e) {
      ByteArrayOutputStream baos = new ByteArrayOutputStream();
      PrintStream out = new PrintStream(baos);
      out.println("Unexpected exception:");
      e.printStackTrace(out);
      fail(baos.toString());
    }
  }

  protected abstract T setup(WellTypedProgram prog)
      throws InvalidProgramException, EvaluationException;

  protected abstract boolean evaluate(T eval) throws EvaluationException;
}
