package edu.harvard.seas.pl.formulog.eval;

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

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.URL;
import java.nio.file.Paths;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ast.ValidProgram;

public abstract class AbstractEvaluationTest {

	protected void test(String file, String inputDir) {
		boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
		try {
			InputStream is = getClass().getClassLoader().getResourceAsStream(file);
			if (is == null) {
				throw new FileNotFoundException(file + " not found");
			}
			URL dir = getClass().getClassLoader().getResource(inputDir);
			Program prog = (new Parser()).parse(new InputStreamReader(is), Paths.get(dir.toURI()));
			WellTypedProgram wellTypedProg = (new TypeChecker(prog)).typeCheck();
			Evaluation eval = setup(wellTypedProg);
			eval.run();
			IndexedFactDB db = eval.getResult();
			ValidProgram vprog = eval.getProgram();
			Symbol sym;
			if (vprog.hasQuery()) {
				sym = vprog.getQuery().getSymbol();
			} else {
				sym = vprog.getSymbolManager().lookupSymbol("ok");
			}
			NormalAtom okAtom = (NormalAtom) Atoms.get(sym, Terms.emptyArray(), false);
			boolean ok = db.hasFact(okAtom);
			if (!ok && !isBad) {
				fail("Test failed for a good program\n" + db);
			}
			if (ok && isBad) {
				fail("Test succeeded for a bad program");
			}
		} catch (Exception e) {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			PrintStream out = new PrintStream(baos);
			out.println("Unexpected exception:");
			e.printStackTrace(out);
			fail(baos.toString());
		}
	}

	protected void test(String file) {
		test(file, "");
	}

	protected abstract Evaluation setup(WellTypedProgram prog)
			throws InvalidProgramException, EvaluationException;

}
