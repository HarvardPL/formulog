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

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Validator;

public class ValidatingTest {

	void test(String file) {
		boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
		try {
			InputStream is = getClass().getClassLoader().getResourceAsStream(file);
			if (is == null) {
				throw new FileNotFoundException(file + " not found");
			}
			Pair<Program, Atom> p = (new Parser()).parse(new InputStreamReader(is));
			Program prog = p.fst();
			Atom query = p.snd();
			prog = (new TypeChecker(prog, query)).typeCheck();
			MagicSetTransformer mst = new MagicSetTransformer(prog);
			if (query != null) {
				p = mst.transform(query, true);
				prog = p.fst();
			} else {
				prog = mst.transform(true);
			}
			(new Validator(prog)).validate();
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
		test("test133_bd.flg");
	}
	
	@Test
	public void test216() {
		test("test216_ok.flg");
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
	
}
