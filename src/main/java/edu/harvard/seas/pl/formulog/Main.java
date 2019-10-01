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

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.nio.file.Paths;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.lang3.time.StopWatch;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.Evaluation;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.EvaluationResult;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public final class Main {

	private final CommandLine cl;
	private final boolean debugMst;
	private final StopWatch clock = new StopWatch();
	private volatile boolean interrupted = true;

	private static final boolean exnStackTrace = System.getProperty("exnStackTrace") != null;

	private Main(CommandLine cl, boolean debugMst) {
		this.cl = cl;
		this.debugMst = debugMst;
	}

	private void go() {
		Program<UserPredicate, BasicRule> prog = parse();
		WellTypedProgram typedProg = typeCheck(prog);
		Evaluation eval = setup(typedProg);
		Runtime.getRuntime().addShutdownHook(
			new Thread() {
			
				@Override
				public void run() {
					if (interrupted) {
						printResults(eval);
					}
				}
				
			}
			
		);
		evaluate(eval);
		interrupted = false;
		printResults(eval);
	}

	private Program<UserPredicate, BasicRule> parse() {
		System.out.print("Parsing... ");
		clock.start();
		try {
			String inputDir = "";
			if (cl.hasOption("I")) {
				inputDir = cl.getOptionValue("I");
			}
			FileReader reader = new FileReader(cl.getArgs()[0]);
			Program<UserPredicate, BasicRule> prog = new Parser().parse(reader, Paths.get(inputDir));
			clock.stop();
			System.out.println(clock.getTime() / 1000.0 + "s");
			return prog;
		} catch (ParseException | FileNotFoundException e) {
			handleException("Error while parsing!", e, true);
			throw new AssertionError("impossible");
		}
	}

	private WellTypedProgram typeCheck(Program<UserPredicate, BasicRule> prog) {
		System.out.print("Type checking... ");
		clock.reset();
		clock.start();
		try {
			WellTypedProgram prog2 = new TypeChecker(prog).typeCheck();
			clock.stop();
			System.out.println(clock.getTime() / 1000.0 + "s");
			return prog2;
		} catch (TypeException e) {
			handleException("Error while typechecking the program!", e, true);
			throw new AssertionError("impossible");
		}
	}

	private Evaluation setup(WellTypedProgram prog) {
		System.out.print("Rewriting and validating... ");
		clock.reset();
		clock.start();
		try {
			Evaluation eval = SemiNaiveEvaluation.setup(prog, Configuration.parallelism);
			clock.stop();
			System.out.println(clock.getTime() / 1000.0 + "s");
			return eval;
		} catch (InvalidProgramException e) {
			handleException("Error while rewriting/validation!", e, true);
			throw new AssertionError("impossible");
		}
	}

	private void evaluate(Evaluation eval) {
		System.out.print("Evaluating... ");
		clock.reset();
		clock.start();
		try {
			eval.run();
			clock.stop();
			System.out.println(clock.getTime() / 1000.0 + "s");
		} catch (EvaluationException e) {
			handleException("Error while evaluating the program!", e, false);
		}
	}

	private void printResults(Evaluation eval) {
		if (Configuration.noResults) {
			return;
		}
		System.out.println("Results:");
		EvaluationResult res = eval.getResult();
		Iterable<UserPredicate> queryRes = res.getQueryAnswer();
		if (queryRes == null || debugMst) {
			PrintStream out = System.out;
			if (debugMst) {
				out = System.err;
				out.println("\n*** All generated facts ***");
			}
			for (RelationSymbol sym : res.getSymbols()) {
				Util.printSortedFacts(res.getAll(sym), out);
			}
		}
		if (queryRes != null) {
			if (debugMst) {
				System.err.println("\n*** Query results ***");
			}
			Util.printSortedFacts(queryRes, System.out);
		}
	}

	private static void printUsageAndDie(Options opts) {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("formulog.jar input-file.flg", opts);
		System.exit(1);
	}

	private static CommandLine parseArgs(String[] args) {
		Options opts = new Options();
		opts.addOption("s", "semiInflationary", false, "Use semi-inflationary evaluation.");
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
		return cl;
	}

	public static void main(String[] args) throws FileNotFoundException {
		CommandLine cl = parseArgs(args);
		(new Main(cl, System.getProperty("debugMst") != null)).go();
	}

	private static void handleException(String msg, Exception e, boolean die) {
		System.out.println(msg);
		System.out.println(e.getMessage());
		if (exnStackTrace) {
			e.printStackTrace(System.out);
		}
		if (die) {
			System.exit(1);
		}
	}

}
