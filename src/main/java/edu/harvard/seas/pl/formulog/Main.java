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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.Callable;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.codegen.CodeGen;
import edu.harvard.seas.pl.formulog.smt.SmtStrategy;
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
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import picocli.CommandLine;
import picocli.CommandLine.*;

@Command(name = "formulog", mixinStandardHelpOptions = true, version = "Formulog 0.5.0", description = "Runs Formulog.")
public final class Main implements Callable<Integer> {

    @Spec
    public static Model.CommandSpec spec;

    @Option(names = "--smt-solver-mode", description = "Strategy to use when interacting with external SMT solvers.", converter = SmtModeConverter.class)
    public static SmtStrategy smtStrategy = Configuration.getSmtStrategy();

    @Option(names = {"-F", "--fact-dir"}, description = "Directory to look for fact .tsv files.")
    public static List<String> factDirs = Configuration.getListProp("factDirs");

    @Option(names = {"-j", "--parallelism"}, description = "Number of threads to use.")
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

    @Parameters(index = "0", description = "Formulog program file.")
    private File file;

    private final StopWatch clock = new StopWatch();
    private volatile boolean interrupted = true;

    private static final boolean exnStackTrace = System.getProperty("exnStackTrace") != null;

    private void go() {
        Program<UserPredicate, BasicRule> prog = parse();
        WellTypedProgram typedProg = typeCheck(prog);
        Evaluation eval = setup(typedProg);
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                    if (interrupted) {
                        printResults(eval);
                    }
                })

        );
        evaluate(eval);
        interrupted = false;
        printResults(eval);
    }

    private Program<UserPredicate, BasicRule> parse() {
        System.out.println("Parsing...");
        clock.start();
        try {
            List<Path> factDirs = Main.factDirs.stream().map(Paths::get).collect(Collectors.toList());
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

    private void printResults(Evaluation eval) {
        PrintStream out = System.out;
        EvaluationResult res = eval.getResult();
        List<RelationSymbol> allSymbols = res.getSymbols().stream().sorted(Comparator.comparing(Object::toString)).collect(Collectors.toList());
        Set<String> stringReprs = allSymbols.stream().map(RelationSymbol::toString).collect(Collectors.toSet());
        for (String sym : relationsToPrint) {
            if (!stringReprs.contains(sym)) {
                out.println("\nWARNING: ignoring unrecognized relation " + sym);
            }
        }
        if (dumpSizes) {
            out.println(getBanner("RELATION SIZES"));
            for (RelationSymbol sym : allSymbols) {
                out.println(sym + "\t" + res.getCount(sym));
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
        List<RelationSymbol> edbSymbols = allSymbols.stream().
                filter(sym -> sym.isEdbSymbol() && (dumpAll || relationsToPrint.contains(sym.toString()))).collect(Collectors.toList());
        printRelations("SELECTED EDB RELATIONS", edbSymbols, res, out);
        List<RelationSymbol> idbSymbols = allSymbols.stream().
                filter(sym -> sym.isIdbSymbol() && (dumpAll || dumpIdb || relationsToPrint.contains(sym.toString()))).collect(Collectors.toList());
        printRelations("SELECTED IDB RELATIONS", idbSymbols, res, out);
    }

    private void printRelations(String heading, Collection<RelationSymbol> symbols, EvaluationResult res, PrintStream out) {
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
            throw new ParameterException(Main.spec.commandLine(), "Unexpected value for SMT solver mode: " + s +
                    " (must be one of 'naive', 'push-pop', or 'check-sat-assuming')");
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
        if (Configuration.codeGen) {
            CodeGen.main(file);
        } else {
            go();
        }
        return 0;
    }
}
