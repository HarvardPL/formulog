package edu.harvard.seas.pl.formulog.magic;

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
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.eval.Interpreter;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;
import edu.harvard.seas.pl.formulog.validating.Validator;

public class MagicTest {

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
				query = p.snd();
			} else {
				prog = mst.transform(true);
			}
			ValidProgram vprog = (new Validator(prog)).validate();
			Interpreter interp = new Interpreter(vprog);
			IndexedFactDB db = interp.run(1);
			boolean ok = false;
			for (Symbol sym : db.getSymbols()) {
				if (query == null && sym.toString().equals("ok") || query != null && sym.equals(query.getSymbol())) {
					ok = true;
					break;
				}
			}
			if (!ok && !isBad) {
				fail("Test failed for a good program");
			}
			if (ok && isBad) {
				fail("Test succeeded for a bad program");
			}
		} catch (Exception e) {
			fail("Unexpected exception: " + e);
		}
	}

	@Test
	public void test140() {
		test("test140_ok.flg");
	}

	@Test
	public void test141() {
		test("test141_ok.flg");
	}

	@Test
	public void test142() {
		test("test142_ok.flg");
	}

	@Test
	public void test143() {
		test("test143_ok.flg");
	}

	@Test
	public void test144() {
		test("test144_ok.flg");
	}

	@Test
	public void test145() {
		test("test145_ok.flg");
	}

	@Test
	public void test146() {
		test("test146_ok.flg");
	}

	@Test
	public void test147() {
		test("test147_ok.flg");
	}

	@Test
	public void test148() {
		test("test148_ok.flg");
	}

	@Test
	public void test149() {
		test("test149_ok.flg");
	}

	@Test
	public void test150() {
		test("test150_ok.flg");
	}

	@Test
	public void test151() {
		test("test151_ok.flg");
	}

	@Test
	public void test152() {
		test("test152_ok.flg");
	}

	@Test
	public void test153() {
		test("test153_ok.flg");
	}

	@Test
	public void test154() {
		test("test154_ok.flg");
	}

	@Test
	public void test155() {
		test("test155_ok.flg");
	}

	@Test
	public void test156() {
		test("test156_ok.flg");
	}

	@Test
	public void test157() {
		test("test157_ok.flg");
	}

	@Test
	public void test158() {
		test("test158_ok.flg");
	}

	@Test
	public void test159() {
		test("test159_ok.flg");
	}

	@Test
	public void test160() {
		test("test160_ok.flg");
	}

	@Test
	public void test161() {
		test("test161_ok.flg");
	}

	@Test
	public void test162() {
		test("test162_ok.flg");
	}

	@Test
	public void test163() {
		test("test163_ok.flg");
	}

	@Test
	public void test164() {
		test("test164_ok.flg");
	}

	@Test
	public void test165() {
		test("test165_ok.flg");
	}

	@Test
	public void test166() {
		test("test166_ok.flg");
	}

	@Test
	public void test167() {
		test("test167_ok.flg");
	}

	@Test
	public void test168() {
		test("test168_ok.flg");
	}

	@Test
	public void test169() {
		test("test169_ok.flg");
	}

	@Test
	public void test170() {
		test("test170_ok.flg");
	}

	@Test
	public void test171() {
		test("test171_ok.flg");
	}
	
	@Test
	public void test172() {
		test("test172_ok.flg");
	}

	@Test
	public void test173() {
		test("test173_ok.flg");
	}

	@Test
	public void test174() {
		test("test174_ok.flg");
	}

	@Test
	public void test175() {
		test("test175_ok.flg");
	}

	@Test
	public void test176() {
		test("test176_ok.flg");
	}

	@Test
	public void test177() {
		test("test177_ok.flg");
	}

	@Test
	public void test178() {
		test("test178_ok.flg");
	}

	@Test
	public void test179() {
		test("test179_ok.flg");
	}

}
