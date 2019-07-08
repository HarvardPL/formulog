package edu.harvard.seas.pl.formulog.magic;

import org.junit.Test;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.eval.Evaluation;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.SemiInflationaryEvaluation;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class SemiInflationaryMagicSetTest extends CommonMagicSetTest {

	@Override
	protected Evaluation setup(WellTypedProgram prog) throws InvalidProgramException, EvaluationException {
		return SemiInflationaryEvaluation.setup(prog, false);
	}
	
	@Test
	public void test224() {
		test("test224_ok.flg");
	}
	
	@Test
	public void test225() {
		test("test225_ok.flg");
	}
	
	@Test
	public void test226() {
		test("test226_ok.flg");
	}
	
	@Test
	public void test227() {
		test("test227_ok.flg");
	}
	
}
