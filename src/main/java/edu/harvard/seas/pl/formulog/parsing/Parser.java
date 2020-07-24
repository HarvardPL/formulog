package edu.harvard.seas.pl.formulog.parsing;

import java.io.FileNotFoundException;

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

import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.atn.PredictionMode;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogLexer;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ProgContext;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

public class Parser {

    private final ParsingContext pc = new ParsingContext();

    private FormulogParser getParser(Reader r, boolean isTsv) throws ParseException {
        try {
            CharStream chars = CharStreams.fromReader(r);
            FormulogLexer lexer = new FormulogLexer(chars);
            TokenStream tokens = isTsv ? new BufferedTokenStream(lexer) : new CommonTokenStream(lexer);
            return new FormulogParser(tokens);
        } catch (IOException e) {
            throw new ParseException(0, e.getMessage());
        }
    }

    public BasicProgram parse(Reader r) throws ParseException {
        return parse(r, Collections.emptyList());
    }

    public BasicProgram parse(Reader r, List<Path> inputDirs) throws ParseException {
        try {
            FormulogParser parser = getParser(r, false);
            ProgContext progCtx = parser.prog();
            Pair<BasicProgram, Set<RelationSymbol>> p = new TopLevelParser(pc).parse(progCtx);
            BasicProgram prog = p.fst();
            loadExternalEdbs(prog, p.snd(), inputDirs);
            return prog;
        } catch (UncheckedParseException e) {
            throw new ParseException(e);
        }
    }

    public Set<Term[]> parseFacts(RelationSymbol sym, Reader factStream) throws ParseException {
        Set<Term[]> facts = new HashSet<>();
        FormulogParser parser = getParser(factStream, true);
        FactFileParser fpp = new FactFileParser(pc);
        fpp.loadFacts(parser.tsvFile(), sym.getArity(), facts);
        return facts;
    }

    private void loadExternalEdbs(Program<UserPredicate, BasicRule> prog, Set<RelationSymbol> rels, List<Path> inputDirs)
            throws ParseException {
        if (rels.isEmpty() || inputDirs.isEmpty()) {
            return;
        }
        ExecutorService exec = Executors.newFixedThreadPool(Configuration.parallelism);
        List<Future<?>> tasks = new ArrayList<>();
        for (Path inputDir : inputDirs) {
            for (RelationSymbol sym : rels) {
                tasks.add(exec.submit(new Runnable() {

                    @Override
                    public void run() {
                        try {
                            readEdbFromFile(sym, inputDir, prog.getFacts(sym));
                        } catch (ParseException e) {
                            throw new UncheckedParseException(e);
                        }
                    }

                }));
            }
        }
        exec.shutdown();
        try {
            for (Future<?> task : tasks) {
                task.get();
            }
        } catch (InterruptedException e) {
            throw new ParseException(0, e.getMessage());
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof UncheckedParseException) {
                throw new ParseException((UncheckedParseException) cause);
            }
            throw new ParseException(0, e.getMessage());
        }
    }

    private void readEdbFromFile(RelationSymbol sym, Path inputDir, Set<Term[]> acc)
            throws ParseException {
        Path path = inputDir.resolve(sym.toString() + ".tsv");
        try (FileReader fr = new FileReader(path.toFile())) {
            FormulogParser parser = getParser(fr, true);
            parser.getInterpreter().setPredictionMode(PredictionMode.SLL);
            FactFileParser fpp = new FactFileParser(pc);
            fpp.loadFacts(parser.tsvFile(), sym.getArity(), acc);
        } catch (FileNotFoundException e) {
            throw new ParseException(0, "Could not find external fact file: " + path);
        } catch (IOException e) {
            throw new ParseException(path.toString(), 0, e.getMessage());
        } catch (UncheckedParseException e) {
            throw new ParseException(path.toString(), e.getLineNo(), e.getMessage());
        } catch (ParseException e) {
            throw new ParseException(path.toString(), e.getLineNo(), e.getMessage());
        }
    }

}
