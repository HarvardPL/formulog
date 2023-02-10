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

import edu.harvard.seas.pl.formulog.Configuration;


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
	public void test128() {
		// Ignoring test (is_free)
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
