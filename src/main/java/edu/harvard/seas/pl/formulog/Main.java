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

import java.io.*;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.Callable;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.codegen.CodeGen;
import edu.harvard.seas.pl.formulog.smt.SmtStrategy;
import org.apache.commons.lang3.time.StopWatch;

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
import picocli.CommandLine;
import picocli.CommandLine.*;
import picocli.CommandLine.Model;

@Command(name = "formulog", mixinStandardHelpOptions = true, version = "Formulog 0.7.0", description = "Runs Formulog.")
public final class Main implements Callable<Integer> {

	@Spec
	private static Model.CommandSpec spec;

	@Option(names = "--smt-solver-mode", description = "Strategy to use when interacting with external SMT solvers"
			+ "('naive', 'push-pop', or 'check-sat-assuming').", converter = SmtModeConverter.class)
	public static SmtStrategy smtStrategy = Configuration.getSmtStrategy();

	@Option(names = { "-F", "--fact-dir" }, description = "Directory to look for fact .tsv files (default: '.').")
	private List<String> factDirs = Configuration.getListProp("factDirs");

	@Option(names = { "-D", "--output-dir" }, description = "Directory for .tsv output files (default: '.').")
	private File outDir = new File(".");

	@Option(names = { "-j", "--parallelism" }, description = "Number of threads to use.")
	public static int parallelism = Configuration.getIntProp("parallelism", 4);

	@Option(names = "--dump-all", description = "Print all relations.")
	private boolean dumpAll;

	@Option(names = "--dump-idb", description = "Print all IDB relations.")
	private boolean dumpIdb;

	@Option(names = "--dump", description = "Print selected relations.")
	private Set<String> relationsToPrint = Collections.emptySet();

	@Option(names = "--dump-query", description = "Print query result.")
	private boolean dumpQuery;

	@Option(names = "--dump-sizes", description = "Print relation sizes.")
	private boolean dumpSizes;

	@Option(names = { "-c", "--codegen" }, description = "Compile the Formulog program.")
	private boolean codegen;

	@Option(names = { "--codegen-dir" }, description = "Directory for generated code (default: './codegen').")
	private File codegenDir = new File("codegen");

	@Option(names = { "--smt-stats" }, description = "Report basic statistics related to SMT solver usage.")
	public static boolean smtStats = false;

	@Parameters(index = "0", description = "Formulog program file.")
	private File file;

	private final StopWatch clock = new StopWatch();
	private volatile boolean interrupted = true;

	private static final boolean exnStackTrace = System.getProperty("exnStackTrace") != null;

	private void go() {
		if (!outDir.mkdirs() && !outDir.exists() || !outDir.isDirectory()) {
			System.out.println("Unable to create output directory: " + outDir);
			System.exit(1);
		}
		BasicProgram prog = parse();
		WellTypedProgram typedProg = typeCheck(prog);
		Evaluation eval = setup(typedProg);
		Runtime.getRuntime().addShutdownHook(new Thread(() -> {
			if (interrupted) {
				dumpResults(eval.getResult());
			}
		})

		);
		evaluate(eval);
		interrupted = false;
		var res = eval.getResult();
		dumpResults(res);
		dumpResultsToDisk(res);
	}

	private BasicProgram parse() {
		System.out.println("Parsing...");
		clock.start();
		try {
			List<Path> factPaths = factDirs.stream().map(Paths::get).collect(Collectors.toList());
			if (factPaths.isEmpty()) {
				factPaths = Collections.singletonList(Paths.get(""));
			}
			FileReader reader = new FileReader(file);
			BasicProgram prog = new Parser().parse(reader, factPaths);
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
			Evaluation eval = SemiNaiveEvaluation.setup(prog, parallelism, Configuration.eagerSemiNaive);
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

	private String getBanner(String heading) {
		return "==================== " + heading + " ====================";
	}

	private String getSmallBanner(String heading) {
		return "---------- " + heading + " ----------";
	}

	private static class FactFileDumper implements Runnable {

		private final Iterable<UserPredicate> facts;
		private final PrintStream out;

		public FactFileDumper(Iterable<UserPredicate> facts, PrintStream out) {
			this.facts = facts;
			this.out = out;
		}

		@Override
		public void run() {
			for (var fact : facts) {
				Term[] args = fact.getArgs();
				for (int i = 0; i < args.length; ++i) {
					out.print(args[i]);
					if (i < args.length - 1) {
						out.print("\t");
					}
				}
				out.println();
			}
			out.close();
		}

	}

	private void dumpResultsToDisk(EvaluationResult res) {
		var pool = Executors.newFixedThreadPool(parallelism);
		try {
			for (RelationSymbol sym : res.getSymbols()) {
				if (sym.isIdbSymbol() && sym.isDisk()) {
					File outFile = outDir.toPath().resolve(sym + ".tsv").toFile();
					boolean ok = outFile.createNewFile();
					if (!ok && !outFile.exists()) {
						throw new IOException("Cannot create output file " + outFile.getName());
					}
					pool.submit(new FactFileDumper(res.getAll(sym), new PrintStream(outFile)));
				}
			}
			pool.shutdown();
			while (!pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS)) {
				// do nothing
			}
		} catch (Exception e) {
			handleException("Problem writing output to disk", e);
		}
	}

	private void dumpResults(EvaluationResult res) {
		PrintStream out = System.out;
		if (smtStats) {
			out.println();
			out.println(getBanner("SMT STATS"));
			out.println("SMT calls: " + Configuration.smtCalls);
			out.println("SMT time (ms): " + Configuration.smtTime);
		}
		List<RelationSymbol> allSymbols = res.getSymbols().stream().sorted(Comparator.comparing(Object::toString))
				.collect(Collectors.toList());
		Set<String> stringReprs = allSymbols.stream().map(RelationSymbol::toString).collect(Collectors.toSet());
		for (String sym : relationsToPrint) {
			if (!stringReprs.contains(sym)) {
				out.println("\nWARNING: ignoring unrecognized relation " + sym);
			}
		}
		if (dumpSizes) {
			out.println();
			out.println(getBanner("RELATION SIZES"));
			for (RelationSymbol sym : allSymbols) {
				out.println(sym + ": " + res.getCount(sym));
			}
		}
		if (dumpAll || dumpQuery) {
			var queryRes = res.getQueryAnswer();
			if (queryRes != null) {
				List<UserPredicate> l = new ArrayList<>();
				queryRes.forEach(l::add);
				out.println();
				out.println(getBanner("QUERY RESULTS (" + l.size() + ")"));
				Util.printSortedFacts(l, out);
			}
		}
		List<RelationSymbol> edbSymbols = allSymbols.stream()
				.filter(sym -> sym.isEdbSymbol() && (dumpAll || relationsToPrint.contains(sym.toString())))
				.collect(Collectors.toList());
		dumpRelations("SELECTED EDB RELATIONS", edbSymbols, res, out);
		List<RelationSymbol> idbSymbols = allSymbols.stream()
				.filter(sym -> sym.isIdbSymbol() && (dumpAll || dumpIdb || relationsToPrint.contains(sym.toString())))
				.collect(Collectors.toList());
		dumpRelations("SELECTED IDB RELATIONS", idbSymbols, res, out);
	}

	private void dumpRelations(String heading, Collection<RelationSymbol> symbols, EvaluationResult res,
			PrintStream out) {
		if (symbols.isEmpty()) {
			return;
		}
		out.println();
		out.println(getBanner(heading));
		for (RelationSymbol sym : symbols) {
			out.println();
			out.println(getSmallBanner(sym + " (" + res.getCount(sym) + ")"));
			if (res.getCount(sym) < 1000) {
				Util.printSortedFacts(res.getAll(sym), out);
			} else {
				for (var tup : res.getAll(sym)) {
					out.println(tup);
				}
			}
		}
	}

	public static class SmtModeConverter implements ITypeConverter<SmtStrategy> {

		@Override
		public SmtStrategy convert(String s) throws Exception {
			switch (s) {
			case "push-pop":
				return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_PUSH_POP, null);
			case "naive":
				return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_PUSH_POP_NAIVE, null);
			case "check-sat-assuming":
				return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_QUEUE, 1);
			}
			throw new ParameterException(Main.spec.commandLine(), "Unexpected value for SMT solver mode: " + s
					+ " (must be one of 'naive', 'push-pop', or 'check-sat-assuming')");
		}
	}

	public static void main(String[] args) throws Exception {
		int exitCode = new CommandLine(new Main()).execute(args);
		System.exit(exitCode);
	}

	private static void handleException(String msg, Exception e) {
		System.out.println(msg);
		System.out.println(e.getMessage());
		if (exnStackTrace) {
			e.printStackTrace(System.out);
		}
		System.exit(1);
	}

	@Override
	public Integer call() throws Exception {
		if (codegen) {
			CodeGen.main(file, codegenDir);
		} else {
			go();
		}
		return 0;
	}
}
