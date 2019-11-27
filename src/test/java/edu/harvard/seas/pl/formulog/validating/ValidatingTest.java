package edu.harvard.seas.pl.formulog.validating;

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

import static org.junit.Assert.fail;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.junit.Test;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.eval.Evaluation;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;

public abstract class ValidatingTest {

	void test(String file) {
		boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
		try {
			InputStream is = getClass().getClassLoader().getResourceAsStream(file);
			if (is == null) {
				throw new FileNotFoundException(file + " not found");
			}
			BasicProgram prog = (new Parser()).parse(new InputStreamReader(is));
			setup(new TypeChecker(prog).typeCheck());
			if (isBad) {
				fail("Test succeeded for a bad program");
			}
		} catch (InvalidProgramException e) {
			if (!isBad) {
				fail("Test failed for a good program");
			}
		} catch (Exception e) {
			fail("Unexpected exception: " + e.getMessage());
		}
	}

	protected abstract Evaluation setup(WellTypedProgram prog) throws InvalidProgramException, EvaluationException;

	@Test
	public void test025() {
		test("test025_bd.flg");
	}

	@Test
	public void test026() {
		test("test026_ok.flg");
	}

	@Test
	public void test050() {
		test("test050_bd.flg");
	}

	@Test
	public void test051() {
		test("test051_bd.flg");
	}

	@Test
	public void test133() {
		test("test133_ok.flg");
	}

	@Test
	public void test217() {
		test("test217_bd.flg");
	}

	@Test
	public void test218() {
		test("test218_bd.flg");
	}

	@Test
	public void test219() {
		test("test219_ok.flg");
	}
	
	@Test
	public void test248() {
		test("test248_bd.flg");
	}
	
	@Test
	public void test251() {
		test("test251_bd.flg");
	}
	
	@Test
	public void test278() {
		test("test278_bd.flg");
	}

}
