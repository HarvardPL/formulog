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

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;

public class CodeGen {

	private final SemiNaiveEvaluation eval;
	private final File outDir;

	public CodeGen(SemiNaiveEvaluation eval, File outDir) {
		this.eval = eval;
		this.outDir = outDir;
	}

	public void go() throws IOException, URISyntaxException {
		copy("Term.hpp");
		CodeGenContext ctx = new CodeGenContext(eval);
		ConstructorSymbolHandler csh = new ConstructorSymbolHandler(ctx);
		RelationHandler rh = new RelationHandler(ctx);
		rh.print(outDir);
		csh.getConstructorsFromTypes(eval.getInputProgram().getTypeSymbols());
		csh.print(outDir);
	}
	
	public void copy(String file) throws IOException, URISyntaxException {
		URL url = getClass().getClassLoader().getResource(file);
		Files.copy(Paths.get(url.toURI()), outDir.toPath().resolve(file));
	}

	private static void clean(File f) {
		if (f.isDirectory()) {
			for (File ff : f.listFiles()) {
				clean(ff);
			}
		}
		f.delete();
	}
	
	public static void main(String[] args) throws Exception {
		if (args.length != 1) {
			throw new IllegalArgumentException("Expected a single argument (the Formulog source file)");
		}
		Program<UserPredicate, BasicRule> prog;
		try (FileReader fr = new FileReader(args[0])) {
			prog = new Parser().parse(fr);
		}
		WellTypedProgram wtp = new TypeChecker(prog).typeCheck();
		SemiNaiveEvaluation eval = SemiNaiveEvaluation.setup(wtp, 4);
		File dir = new File("codegen");
		clean(dir);
		dir.mkdirs();
		new CodeGen(eval, dir).go();
	}

}
