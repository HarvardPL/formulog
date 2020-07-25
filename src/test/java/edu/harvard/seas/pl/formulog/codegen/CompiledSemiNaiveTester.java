package edu.harvard.seas.pl.formulog.codegen;

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

import java.io.BufferedReader;
import java.io.File;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.eval.AbstractTester;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class CompiledSemiNaiveTester extends AbstractTester<SemiNaiveEvaluation> {

	private List<String> inputDirs = Collections.emptyList();

	@Override
	public void test(String file, List<String> inputDirs) {
		this.inputDirs = inputDirs;
		super.test(file, Collections.emptyList());
	}

	@Override
	protected SemiNaiveEvaluation setup(WellTypedProgram prog) throws InvalidProgramException, EvaluationException {
		return SemiNaiveEvaluation.setup(prog, 2, false);
	}

	@Override
	protected boolean evaluate(SemiNaiveEvaluation eval) throws EvaluationException {
		File dir = new File("codegen");
		Util.clean(dir, false);
		dir.mkdirs();
		Path path = dir.toPath();
		CodeGen cg = new CodeGen(eval, dir);
		try {
			cg.go();
			Process proc = Runtime.getRuntime().exec(
					new String[] { "make", "-C", path.toString(), "-j", String.valueOf(Configuration.parallelism) });
			if (proc.waitFor() != 0) {
				System.err.println("Could not compile test");
				printToStdErr(proc.getErrorStream());
				return false;
			}
			String cmd = path.resolve("flg").toString();
			for (String inputDir : inputDirs) {
				Path p = Paths.get(getClass().getClassLoader().getResource(inputDir).toURI());
				cmd += " --fact-dir " + p;
			}
			proc = Runtime.getRuntime().exec(cmd);
			if (proc.waitFor() != 0) {
				System.err.println("Evaluation error");
				printToStdErr(proc.getErrorStream());
				return false;
			}
			BufferedReader br = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			String line;
			while ((line = br.readLine()) != null) {
				if (line.equals("ok: 1")) {
					return true;
				}
			}
			return false;
		} catch (IOException | URISyntaxException | InterruptedException e) {
			throw new EvaluationException(e);
		}
	}

	private static void printToStdErr(InputStream is) throws IOException {
		BufferedReader br = new BufferedReader(new InputStreamReader(is));
		String line;
		while ((line = br.readLine()) != null) {
			System.err.println(line);
		}
	}

}
