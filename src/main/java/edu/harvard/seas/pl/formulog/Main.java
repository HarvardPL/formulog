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

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.Interpreter;
import edu.harvard.seas.pl.formulog.magic.MagicTransformer;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;
import edu.harvard.seas.pl.formulog.validating.Validator;

public final class Main {

	private Main() {
		throw new AssertionError();
	}

	private static void printUsageAndDie(Options opts) {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("formulog.jar input-file.flg", opts);
		System.exit(1);
	}
	
	private static CommandLine parseArgs(String[] args) {
		Options opts = new Options();
		opts.addOption("j", true, "Number of threads to use (defaults to 1).");
		opts.addOption("v", "verbose", false, "Print a lot of stuff.");
		CommandLineParser clp = new DefaultParser();
		CommandLine cl = null;
		try {
			cl = clp.parse(opts, args);
		} catch (org.apache.commons.cli.ParseException e) {
			System.out.println(e.getMessage());
			printUsageAndDie(opts);
		}
		if (cl.getArgs().length != 1) {
			System.out.println("You need to supply one (and only one) FormuLog file.");
			printUsageAndDie(opts);
		}
		if (cl.hasOption("v")) {
			System.setProperty("debugMst", "true");
			System.setProperty("debugSmt", "true");
			System.setProperty("factTrace", "true");
		}
		return cl;
	}

	public static void main(String[] args) throws FileNotFoundException {
		CommandLine cl = parseArgs(args);
		System.out.println("Parsing program...");
		Pair<Program, Atom> p = null;
		try {
			p = (new Parser()).parse(new FileReader(args[0]));
		} catch (ParseException e) {
			handleException("Error while parsing!", e);
		}
		Program prog = p.fst();
		Atom q = p.snd();
		System.out.println("Type checking...");
		TypeChecker typeChecker = new TypeChecker(prog, q);
		try {
			prog = typeChecker.typeCheck();
		} catch (TypeException e) {
			handleException("Error while typechecking the program!", e);
		}
		if (q != null) {
			System.out.println("Rewriting for query " + q + "...");
			try {
				prog = (new MagicTransformer(prog, q)).transform();
			} catch (InvalidProgramException e) {
				handleException("Error while rewriting the program!", e);
			}
			if (System.getProperty("debugMst") != null) {
				System.out.println("\n*** New rules ***");
				List<String> rules = new ArrayList<>();
				for (Symbol sym : prog.getRuleSymbols()) {
					for (Rule r : prog.getRules(sym)) {
						rules.add(r.toString());
					}
				}
				Collections.sort(rules);
				for (String r : rules) {
					System.out.println(r);
				}
				System.out.println();
			}
		}
		System.out.println("Validating...");
		ValidProgram vprog = null;
		try {
			vprog = (new Validator(prog)).validate();
		} catch (InvalidProgramException e) {
			handleException("Error while rewriting the program!", e);
		}
		System.out.println("Evaluating...");
		Interpreter interp = new Interpreter(vprog);
		try {
			int nthreads = cl.hasOption("j") ? Integer.parseInt(cl.getOptionValue("j")) : 1;
			interp.run(nthreads);
		} catch (EvaluationException e) {
			handleException("Error while evaluating the program!", e);
		}
		System.out.println("Results:");
		IndexedFactDB db = interp.getResult();
		if (q == null || System.getProperty("debugSmt") != null) {
			System.out.println("\n*** All generated facts ***");
			for (Symbol sym : db.getSymbols()) {
				printSortedFacts(db.query(sym));
			}
		}
		if (q != null) {
			System.out.println("\n*** Query results ***");
			printSortedFacts(db.query(q.getSymbol()));
		}
	}

	private static void printSortedFacts(Iterable<NormalAtom> facts) {
		Util.iterableToList(facts).stream().map(a -> {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			PrintStream ps = new PrintStream(baos);
			ps.print(a);
			return baos.toString();
		}).sorted().forEach(s -> System.out.println(s));
	}

	private static void handleException(String msg, Exception e) {
		System.out.println(msg);
		System.out.println(e.getMessage());
		System.exit(1);
	}

}
