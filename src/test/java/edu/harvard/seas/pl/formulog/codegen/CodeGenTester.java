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
package edu.harvard.seas.pl.formulog.codegen;

import static org.junit.Assert.fail;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.Main;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.eval.Tester;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class CodeGenTester implements Tester {

  private List<String> inputDirs = Collections.emptyList();
  private final boolean eagerEval;

  public CodeGenTester(boolean eagerEval) {
    this.eagerEval = eagerEval;
  }

  @Override
  public void test(String file, List<String> inputDirs) {
    boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
    Path topPath = null;
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
      WellTypedProgram wtp = new TypeChecker(prog).typeCheck();
      MagicSetTransformer mst = new MagicSetTransformer(wtp);
      BasicProgram magicProg = mst.transform(true, true);
      String name = file.substring(0, file.indexOf('.'));
      topPath = Path.of("codegen", "tests", name);
      boolean ok = evaluate(name, topPath, magicProg);
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
    } finally {
      if (!Configuration.keepCodeGenTestDirs && topPath != null) {
        Util.clean(topPath.toFile(), true);
      }
    }
  }

  private boolean evaluate(String name, Path topPath, BasicProgram prog) throws Exception {
    File srcDir = topPath.resolve("src").toFile();
    srcDir.mkdirs();
    Util.clean(srcDir, false);
    Path buildPath = topPath.resolve("build");
    CodeGen cg = new CodeGen(prog, topPath.toFile());
    cg.go();
    var cmakeCmds =
        new ArrayList<>(
            Arrays.asList(
                "cmake",
                "-B",
                buildPath.toString(),
                "-S",
                topPath.toString(),
                "-DCMAKE_BUILD_TYPE=Debug"));
    if (eagerEval) {
      cmakeCmds.add("-DFLG_EAGER_EVAL=On");
    }
    if (Configuration.cxxCompiler != null) {
      cmakeCmds.add("-DCMAKE_CXX_COMPILER=" + Configuration.cxxCompiler);
    }
    Process cmake = Runtime.getRuntime().exec(cmakeCmds.toArray(new String[0]));
    if (cmake.waitFor() != 0) {
      System.err.println("Could not cmake test");
      printToStdErr(cmake.getErrorStream());
      return false;
    }

    Process make =
        Runtime.getRuntime()
            .exec(
                new String[] {
                  "cmake", "--build", buildPath.toString(), "-j", String.valueOf(Main.parallelism)
                });
    if (make.waitFor() != 0) {
      System.err.println("Could not make test");
      printToStdErr(make.getErrorStream());
      return false;
    }

    String cmd = topPath.resolve("build").resolve("flg").toString();
    for (String inputDir : inputDirs) {
      Path p = Paths.get(getClass().getClassLoader().getResource(inputDir).toURI());
      cmd += " --fact-dir " + p;
    }
    cmd += " --dump-sizes -j 4";

    Process flg = Runtime.getRuntime().exec(cmd);
    if (flg.waitFor() != 0) {
      System.err.println("Evaluation error");
      printToStdErr(flg.getErrorStream());
      return false;
    }

    BufferedReader br = new BufferedReader(new InputStreamReader(flg.getInputStream()));
    String line;
    while ((line = br.readLine()) != null) {
      if (line.equals("ok: 1") || line.equals("query__ok: 1")) {
        return true;
      }
    }
    return false;
  }

  private static void printToStdErr(InputStream is) throws IOException {
    BufferedReader br = new BufferedReader(new InputStreamReader(is));
    String line;
    while ((line = br.readLine()) != null) {
      System.err.println(line);
    }
  }
}
