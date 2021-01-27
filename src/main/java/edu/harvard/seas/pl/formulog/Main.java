package edu.harvard.seas.pl.formulog;

/*-
 * #%L
 * Formulog
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

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.commons.lang3.time.StopWatch;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.codegen.CodeGen;
import edu.harvard.seas.pl.formulog.eval.Evaluation;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.EvaluationResult;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public final class Main {

	private final String file;
	private final StopWatch clock = new StopWatch();
	private volatile boolean interrupted = true;

	private static final boolean exnStackTrace = System.getProperty("exnStackTrace") != null;

	private Main(String file) {
		this.file = file;
	}

	private void go() {
		Program<UserPredicate, BasicRule> prog = parse();
		WellTypedProgram typedProg = typeCheck(prog);
		Evaluation eval = setup(typedProg);
		Runtime.getRuntime().addShutdownHook(new Thread() {

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
		System.out.println("Parsing...");
		clock.start();
		try {
			List<Path> factDirs = Configuration.factDirs.stream().map(Paths::get).collect(Collectors.toList());
			if (factDirs.isEmpty()) {
				factDirs = Collections.singletonList(Paths.get(""));
			}
			FileReader reader = new FileReader(file);
			Program<UserPredicate, BasicRule> prog = new Parser().parse(reader, factDirs);
			clock.stop();
			System.out.println("Finished parsing (" + clock.getTime() / 1000.0 + "s)");
			return prog;
		} catch (FileNotFoundException e) {
			handleException("Error while parsing!", e);
		} catch (ParseException e) {
			String msg = "Error while parsing ";
			if (e.getFileName() != null) {
				msg += e.getFileName() + ", ";
			}
			msg += "line " + e.getLineNo() + ":";
			handleException(msg, e);
		}
		throw new AssertionError("impossible");
	}

	private WellTypedProgram typeCheck(Program<UserPredicate, BasicRule> prog) {
		System.out.println("Type checking...");
		clock.reset();
		clock.start();
		try {
			WellTypedProgram prog2 = new TypeChecker(prog).typeCheck();
			clock.stop();
			System.out.println("Finished type checking (" + clock.getTime() / 1000.0 + "s)");
			return prog2;
		} catch (TypeException e) {
			handleException("Error while typechecking the program!", e);
			throw new AssertionError("impossible");
		}
	}

	private Evaluation setup(WellTypedProgram prog) {
		System.out.println("Rewriting and validating...");
		clock.reset();
		clock.start();
		try {
			Evaluation eval = SemiNaiveEvaluation.setup(prog, Configuration.parallelism, Configuration.eagerSemiNaive);
			clock.stop();
			System.out.println("Finished rewriting and validating (" + clock.getTime() / 1000.0 + "s)");
			return eval;
		} catch (InvalidProgramException e) {
			handleException("Error while rewriting/validation!", e);
			throw new AssertionError("impossible");
		}
	}

	private void evaluate(Evaluation eval) {
		System.out.println("Evaluating...");
		clock.reset();
		clock.start();
		try {
			eval.run();
			clock.stop();
			System.out.println("Finished evaluating (" + clock.getTime() / 1000.0 + "s)");
		} catch (EvaluationException e) {
			handleException("Error while evaluating the program!", e);
		}
	}

	private void printResults(Evaluation eval) {
		PrintStream out = System.out;
		EvaluationResult res = eval.getResult();
		switch (Configuration.printResultsPreference) {
		case ALL:
			printEdb(res, out);
			out.println();
			printIdb(res, out);
			break;
		case EDB:
			printEdb(res, out);
			break;
		case IDB:
			printIdb(res, out);
			break;
		case QUERY:
			printQueryResults(res, out);
			break;
		case SOME:
			printSelectedResults(res, eval.getInputProgram().getSymbolManager(), out);
			break;
		case NONE:
			break;
		}
	}

	public void printEdb(EvaluationResult res, PrintStream out) {
		out.println("Extensional database:");
		for (RelationSymbol sym : res.getSymbols()) {
			if (sym.isEdbSymbol()) {
				Util.printSortedFacts(res.getAll(sym), out);
			}
		}
	}

	public void printIdb(EvaluationResult res, PrintStream out) {
		out.println("Intensional database:");
		for (RelationSymbol sym : res.getSymbols()) {
			if (sym.isIdbSymbol()) {
				Util.printSortedFacts(res.getAll(sym), out);
			}
		}
	}

	public void printQueryResults(EvaluationResult res, PrintStream out) {
		out.println("Query results:");
		Iterable<UserPredicate> ans = res.getQueryAnswer();
		if (ans == null) {
			out.println("[there was no query]");
		} else {
			Util.printSortedFacts(res.getQueryAnswer(), out);
		}
	}

	public void printSelectedResults(EvaluationResult res, SymbolManager sm, PrintStream out) {
		out.println("Selected results:");
		for (String name : Configuration.getSelectedRelsToPrint()) {
			if (!sm.hasName(name)) {
				out.println("[ignoring unrecognized symbol: " + name + "]");
				continue;
			}
			Symbol sym = sm.lookupSymbol(name);
			if (!(sym instanceof RelationSymbol)) {
				out.println("[ignoring symbol " + name + " (not a relation symbol)]");
			}
		}
		for (RelationSymbol sym : res.getSymbols()) {
			if (Configuration.getSelectedRelsToPrint().contains(sym.toString())) {
				Util.printSortedFacts(res.getAll(sym), out);
			}
		}
	}

	public static void main(String[] args) throws Exception {
		if (Configuration.runTests) {
			try {
			FormulogTester.main(args);
			} catch (Exception e) {
				handleException("Problem running test suite", e);
			}
		} else if (Configuration.codeGen) {
			CodeGen.main(args);
		} else {
			if (args.length != 1) {
				System.out.println("Expected a single Formulog file as an argument.");
				System.exit(1);
			}
			new Main(args[0]).go();
		}
	}

	private static void handleException(String msg, Exception e) {
		System.out.println(msg);
		System.out.println(e.getMessage());
		if (exnStackTrace) {
			e.printStackTrace(System.out);
		}
		System.exit(1);
	}

}
