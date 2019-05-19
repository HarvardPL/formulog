package edu.harvard.seas.pl.formulog;

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

import java.io.FileReader;
import java.util.Iterator;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.eval.Interpreter;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;
import edu.harvard.seas.pl.formulog.validating.Validator;

public class Time {

	private Time() {
		throw new AssertionError();
	}

	private static CommandLine parseArgs(String[] args) throws ParseException {
		Options opts = new Options();
		opts.addOption("j", true, "Number of threads to use (defaults to 1).");
		opts.addOption("v", "verbose", false, "Print size of computed relations.");
		CommandLineParser clp = new DefaultParser();
		CommandLine cl = clp.parse(opts, args);
		if (cl.getArgs().length != 1) {
			System.err.println("You need to supply one (and only one) FormuLog file.");
			System.exit(1);
		}
		return cl;
	}

	public static void main(String[] args) throws Exception {
		long start = System.currentTimeMillis();
		CommandLine cl = parseArgs(args);
		Pair<Program, Atom> p = (new Parser()).parse(new FileReader(args[0]));
		Program prog = p.fst(); 
		Atom q = p.snd();
		prog = (new TypeChecker(prog, q)).typeCheck();
		if (q != null) {
			p = (new MagicSetTransformer(prog)).transform(q, false);
			prog = p.fst();
		}
		ValidProgram vprog = (new Validator(prog)).validate();
		Interpreter interp = new Interpreter(vprog);
		int nthreads = cl.hasOption("j") ? Integer.parseInt(cl.getOptionValue("j")) : 1;
		IndexedFactDB db = interp.run(nthreads);
		long end = System.currentTimeMillis();
		System.out.println((end - start) / 1000.0);
		if (cl.hasOption("v")) {
			for (Symbol sym : db.getSymbols()) {
				int i = 0;
				for (Iterator<NormalAtom> it = db.query(sym).iterator(); it.hasNext(); ++i, it.next()) {

				}
				System.out.println(sym + ":\t" + i);
			}
		}
	}

}
