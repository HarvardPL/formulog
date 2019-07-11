package edu.harvard.seas.pl.formulog.eval;

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

import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class SemiInflationaryEvaluationTest extends CommonEvaluationTest {

	@Override
	protected Evaluation setup(WellTypedProgram prog) throws InvalidProgramException, EvaluationException {
		assert !prog.hasQuery();
		return SemiInflationaryEvaluation.setup(prog, true);
	}
	
	@Test
	public void test220() {
		test("test220_ok.flg");
	}
	
	@Test
	public void test221() {
		test("test221_ok.flg");
	}
	
	@Test
	public void test222() {
		test("test222_ok.flg");
	}
	
	@Test
	public void test223() {
		test("test223_ok.flg");
	}
	
	@Test
	public void test228() {
		test("test228_ok.flg");
	}
	
	@Test
	public void test229() {
		test("test229_ok.flg");
	}
	
	@Test
	public void test230() {
		test("test230_ok.flg");
	}
	
	@Test
	public void test231() {
		test("test231_ok.flg");
	}
	
	@Test
	public void test236() {
		test("test236_ok.flg");
	}
	
	@Test
	public void test240() {
		test("test240_ok.flg");
	}

}
