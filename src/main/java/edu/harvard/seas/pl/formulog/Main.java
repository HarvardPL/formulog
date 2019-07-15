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
import java.nio.file.Paths;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;

import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.eval.Evaluation;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.EvaluationResult;
import edu.harvard.seas.pl.formulog.eval.SemiInflationaryEvaluation;
import edu.harvard.seas.pl.formulog.eval.StratifiedEvaluation;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ast.ValidProgram;

public final class Main {

	private final CommandLine cl;
	private final boolean debugMst; 
	
	private Main(CommandLine cl, boolean debugMst) {
		this.cl = cl;
		this.debugMst = debugMst;
	}

	private void go() {
		Program prog = parse();
		WellTypedProgram typedProg = typeCheck(prog);
		Evaluation eval = setup(typedProg);
		evaluate(eval);
		printResults(eval);
	}
	
	private Program parse() {
		System.out.println("Parsing...");
		try {
			String inputDir = "";
			if (cl.hasOption("I")) {
				inputDir = cl.getOptionValue("I");
			}
			FileReader reader = new FileReader(cl.getArgs()[0]);
			return (new Parser()).parse(reader, Paths.get(inputDir));
		} catch (ParseException | FileNotFoundException e) {
			handleException("Error while parsing!", e);
			throw new AssertionError("impossible");
		}
	}
	
	private WellTypedProgram typeCheck(Program prog) {
		System.out.println("Type checking...");
		TypeChecker typeChecker = new TypeChecker(prog);
		try {
			return typeChecker.typeCheck();
		} catch (TypeException e) {
			handleException("Error while typechecking the program!", e);
			throw new AssertionError("impossible");
		}
	}
	
	private Evaluation setup(WellTypedProgram prog) {
		System.out.println("Rewriting and validating...");
		try {
			if (cl.hasOption("s")) {
				return SemiInflationaryEvaluation.setup(prog, true);
			} else {
				return StratifiedEvaluation.setup(prog, true);
			}
		} catch (InvalidProgramException e) {
			handleException("Error while rewriting/validation!", e);
			throw new AssertionError("impossible");
		}
	}
	
	private void evaluate(Evaluation eval) {
		System.out.println("Evaluating...");
		try {
			int parallelism = cl.hasOption("j") ? Integer.valueOf(cl.getOptionValue("j")) : 1;
			eval.run(parallelism);
		} catch (EvaluationException e) {
			handleException("Error while evaluating the program!", e);
		}
	}
	
	private void printResults(Evaluation eval) {
		System.out.println("Results:");
		EvaluationResult res = eval.getResult();
		ValidProgram vprog = eval.getProgram();
		if (!vprog.hasQuery() || debugMst) {
			PrintStream out = System.out;
			if (debugMst) {
				out = System.err;
				out.println("\n*** All generated facts ***");
			}
			for (Symbol sym : res.getSymbols()) {
				printSortedFacts(res.getAll(sym), out);
			}
		}
		if (vprog.hasQuery()) {
			if (debugMst) {
				System.err.println("\n*** Query results ***");
			}
			printSortedFacts(res.getQueryAnswer(), System.out);
		}
	}
	
	private static void printUsageAndDie(Options opts) {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("formulog.jar input-file.flg", opts);
		System.exit(1);
	}

	private static CommandLine parseArgs(String[] args) {
		Options opts = new Options();
		opts.addOption("j", true, "Number of threads to use (defaults to 1).");
		opts.addOption("s", "semiInflationary", false, "Use semi-inflationary evaluation.");
		opts.addOption("v", "verbose", false, "Print a lot of stuff.");
		opts.addOption("I", true, "Directory for (tab and/or space-delimited) CSVs with input facts.");
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
			System.setProperty("callTrace", "true");
		}
		return cl;
	}

	public static void main(String[] args) throws FileNotFoundException {
		CommandLine cl = parseArgs(args);
		(new Main(cl, System.getProperty("debugMst") != null)).go();
	}

	private static void printSortedFacts(Iterable<NormalAtom> facts, PrintStream out) {
		Util.iterableToList(facts).stream().map(a -> {
			ByteArrayOutputStream baos = new ByteArrayOutputStream();
			PrintStream ps = new PrintStream(baos);
			ps.print(a);
			return baos.toString();
		}).sorted().forEach(s -> out.println(s));
	}

	private static void handleException(String msg, Exception e) {
		System.out.println(msg);
		System.out.println(e.getMessage());
		System.exit(1);
	}

}
