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

import org.junit.Test;

public class BalbinEvaluationComparisonTest extends AbstractEvaluationTest {

	public BalbinEvaluationComparisonTest() {
		super(new BalbinComparisonTester());
	}

	// TODO: Update tests

//	@Test
//	public void test001() { test("balbin_comparison/test001_ok.flg"); }

	@Test
	public void test002() { test("balbin_comparison/test002_ok.flg"); }
//
//	@Test
//	public void test003() { test("balbin_comparison/test003_ok.flg"); }

}
