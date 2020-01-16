package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * FormuLog
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

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;

import edu.harvard.seas.pl.formulog.eval.AbstractTester;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class CompiledSemiNaiveTester extends AbstractTester<SemiNaiveEvaluation> {

	@Override
	protected SemiNaiveEvaluation setup(WellTypedProgram prog) throws InvalidProgramException, EvaluationException {
		return SemiNaiveEvaluation.setup(prog, 2);
	}

	@Override
	protected boolean evaluate(SemiNaiveEvaluation eval) throws EvaluationException {
		Path outDir = Paths.get("codegen");
		CodeGen cg = new CodeGen(eval, outDir.toFile());
		try {
			cg.go();
		} catch (IOException | URISyntaxException e) {
			throw new EvaluationException(e);
		}
		// Create process to run g++
		// Create process to run executable
		// Check output for `ok: 1` line
		return false;
	}


}
