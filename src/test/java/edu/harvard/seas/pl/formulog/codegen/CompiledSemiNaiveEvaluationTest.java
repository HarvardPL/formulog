package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.Configuration;

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

import edu.harvard.seas.pl.formulog.eval.CommonEvaluationTest;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;

public class CompiledSemiNaiveEvaluationTest extends CommonEvaluationTest<SemiNaiveEvaluation> {

	static {
		if (!Configuration.testCodeGen) {
			System.err.println("WARNING: skipping CompiledSemiNaiveEvaluationTest; enable with flag");
		}
	}
	
	public CompiledSemiNaiveEvaluationTest() {
		super(Configuration.testCodeGen ? new CompiledSemiNaiveTester() : new NopTester<>());
	}
	
	@Override
	public void test061() {
		// Ignoring test (substitute)
	}
	
	@Override
	public void test096() {
		// Ignoring test (substitute)
	}
	
	@Override
	public void test097() {
		// Ignoring test (substitute)
	}

	@Override
	public void test099() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test100() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test102() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test103() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test104() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test105() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test106() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test107() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test108() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test109() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test110() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test111() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test112() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test113() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test114() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test115() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test116() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test128() {
		// Ignoring test (is_free)
	}
	
	@Override
	public void test135() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test137() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test190() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test254() {
		// Ignoring test (get_model)
	}
	
	@Override
	public void test283() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test284() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test285() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test286() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test287() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test290() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test291() {
		// Ignoring test (fold)
	}
	
	@Override
	public void test292() {
		// Ignoring test (fold)
	}

}
