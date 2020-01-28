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
import java.nio.file.Path;
import java.nio.file.Paths;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;

public class CodeGen {

	private final SemiNaiveEvaluation eval;
	private final File outDir;

	public CodeGen(SemiNaiveEvaluation eval, File outDir) {
		this.eval = eval;
		this.outDir = outDir;
	}

	public void go() throws IOException, URISyntaxException {
		copy("Term.hpp");
		copy("FactParser.hpp");
		copy("parsing");
		CodeGenContext ctx = new CodeGenContext(eval);
		new RelsHpp(ctx).gen(outDir);
		new FuncsHpp(ctx).gen(outDir);
		new MainCpp(ctx).gen(outDir);
		new SmtHpp(ctx).gen(outDir);
		new TypeHpp(ctx).gen(outDir);
		new SymbolHpp(ctx).print(outDir);
		new CompileSh().print(outDir);
	}
	
	private void copy(String file) throws IOException, URISyntaxException {
		URL url = getClass().getClassLoader().getResource(file);
		copy(Paths.get(url.toURI()).toFile(), outDir.toPath());
	}
	
	private void copy(File fileToCopy, Path outDir) throws IOException {
		String name = fileToCopy.getName();
		Path dest = outDir.resolve(name);
		Files.copy(fileToCopy.toPath(), dest);
		String ext = name.substring(name.lastIndexOf('.') + 1);
		if (ext.equals("sh")) {
			dest.toFile().setExecutable(true);
		}
		if (fileToCopy.isDirectory()) {
			for (File child : fileToCopy.listFiles()) {
				copy(child, dest);
			}
		}
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
		Util.clean(dir, false);
		dir.mkdirs();
		new CodeGen(eval, dir).go();
	}

}
