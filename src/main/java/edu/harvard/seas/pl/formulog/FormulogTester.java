package edu.harvard.seas.pl.formulog;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2021 President and Fellows of Harvard College
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
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.Evaluation;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.eval.EvaluationResult;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.sexp.SExp;
import edu.harvard.seas.pl.formulog.util.sexp.SExpException;
import edu.harvard.seas.pl.formulog.util.sexp.SExpParser;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class FormulogTester {

	private boolean initialized;
	private final List<FormulogTest> tests = new ArrayList<>();
	private WellTypedProgram prog;

	public synchronized void setup(Reader program, File testFile) throws ParseException, TypeException, IOException {
		Parser parser = new Parser();
		prog = new TypeChecker(parser.parse(program)).typeCheck();
		loadTests(testFile, parser);
		initialized = true;
	}

	private void loadTests(File testFile, Parser parser) throws IOException, ParseException {
		tests.clear();
		ObjectMapper objectMapper = new ObjectMapper();
		JsonNode topLevel = objectMapper.readValue(testFile, JsonNode.class);
		Path rootTestDir = testFile.getParentFile().toPath();
		for (JsonNode test : topLevel) {
			tests.add(loadTest(test, rootTestDir, parser));
		}
	}

	private FormulogTest loadTest(JsonNode test, Path rootTestDir, Parser parser)
			throws ParseException, FileNotFoundException {
		String name = test.get("name").asText();
		Path dir = rootTestDir.resolve(name);
		Map<RelationSymbol, Set<Term[]>> m = new HashMap<>();
		for (RelationSymbol sym : prog.getFactSymbols()) {
			if (sym.isEdbSymbol()) {
				FileReader fr = new FileReader(dir.resolve(sym + ".tsv").toFile());
				Set<Term[]> s = parser.parseFacts(sym, fr);
				m.put(sym, s);
			}
		}
		try {
			Function<EvaluationResult, List<String>> logic = parseBoolLogic(test.get("spec").asText());
			return new FormulogTest(name, m, logic);
		} catch (ParseException e) {
			throw new ParseException(-1, "Trouble parsing spec for test " + name + ": " + e.getMessage());
		}
	}

	private Function<EvaluationResult, List<String>> parseBoolLogic(String s) throws ParseException {
		Reader r = new StringReader(s);
		SExpParser p = new SExpParser(r);
		SExp sexp;
		try {
			sexp = p.parse();
		} catch (SExpException e) {
			throw new ParseException(-1, e.getMessage());
		}
		return parseBoolLogic(sexp);
	}

	private Function<EvaluationResult, List<String>> parseBoolLogic(SExp sexp) throws ParseException {
		if (sexp.isAtom()) {
			return parseBoolAtom(sexp.asAtom());
		} else {
			return parseBoolList(sexp.asList());
		}
	}

	private Function<EvaluationResult, List<String>> parseBoolAtom(String atom) throws ParseException {
		switch (atom) {
		case "true":
			return r -> Collections.emptyList();
		default:
			throw new ParseException(-1, "Unrecognized boolean constant: " + atom);
		}
	}

	private Function<EvaluationResult, List<String>> parseBoolList(List<SExp> l) throws ParseException {
		if (l.isEmpty()) {
			throw new ParseException(-1, "Unexpected empty list");
		}
		SExp head = l.get(0);
		if (head.isList()) {
			throw new ParseException(-1, "Expected an operator, but got a list: " + head);
		}
		String cmd = head.asAtom();
		switch (cmd) {
		case "=": {
			if (l.size() != 3) {
				throw new ParseException(-1, "Wrong number of arguments for = operator: " + l.size());
			}
			SExp sexp1 = l.get(1);
			SExp sexp2 = l.get(2);
			Function<EvaluationResult, Integer> f1 = parseIntLogic(sexp1);
			Function<EvaluationResult, Integer> f2 = parseIntLogic(sexp2);
			return r -> {
				int v1 = f1.apply(r);
				int v2 = f2.apply(r);
				if (v1 == v2) {
					return Collections.emptyList();
				} else {
					return Collections.singletonList(
							"Failed equality: (= " + sexp1 + " " + sexp2 + ") reduces to (= " + v1 + " " + v2 + ")");
				}
			};
		}
		case "and": {
			List<Function<EvaluationResult, List<String>>> fs = new ArrayList<>();
			for (Iterator<SExp> it = l.listIterator(1); it.hasNext();) {
				fs.add(parseBoolLogic(it.next()));
			}
			return r -> {
				List<String> errors = new ArrayList<>();
				for (Function<EvaluationResult, List<String>> f : fs) {
					errors.addAll(f.apply(r));
				}
				return errors;
			};
		}
		default:
			throw new ParseException(-1, "Unrecognized boolean operator: " + cmd);
		}
	}

	private Function<EvaluationResult, Integer> parseIntLogic(SExp sexp) throws ParseException {
		if (sexp.isAtom()) {
			return parseIntAtom(sexp.asAtom());
		} else {
			return parseIntList(sexp.asList());
		}
	}

	private Function<EvaluationResult, Integer> parseIntAtom(String s) throws ParseException {
		try {
			int n = Integer.parseInt(s);
			return r -> n;
		} catch (NumberFormatException e) {
			throw new ParseException(-1, "Expected an integer constant but got " + s);
		}
	}

	private Function<EvaluationResult, Integer> parseIntList(List<SExp> l) throws ParseException {
		if (l.isEmpty()) {
			throw new ParseException(-1, "Unexpected empty list");
		}
		SExp head = l.get(0);
		if (head.isList()) {
			throw new ParseException(-1, "Expected an operator, but got a list: " + head);
		}
		String cmd = head.asAtom();
		switch (cmd) {
		case "size":
			if (l.size() != 2) {
				throw new ParseException(-1, "Wrong number of arguments for size operator: " + l.size());
			}
			SExp sexp1 = l.get(1);
			if (sexp1.isList()) {
				throw new ParseException(-1, "size operator expects a relation symbol, but got a list: " + sexp1);
			}
			String name = sexp1.asAtom();
			SymbolManager sm = prog.getSymbolManager();
			if (!sm.hasName(name)) {
				throw new ParseException(-1, "unrecognized relation used in size operator: " + name);
			}
			Symbol sym = sm.lookupSymbol(name);
			if (!(sym instanceof RelationSymbol)) {
				throw new ParseException(-1, "non-relation symbol used in size operator: " + name);
			}
			RelationSymbol rel = (RelationSymbol) sym;
			return r -> r.getCount(rel);
		default:
			throw new ParseException(-1, "Unrecognized integer operator: " + cmd);
		}
	}

	synchronized boolean runTests() throws InvalidProgramException, EvaluationException {
		if (!initialized) {
			throw new IllegalStateException("Need to set up tests first.");
		}
		// Need to get the EDBs that are hard-coded into the program.
		Map<RelationSymbol, Set<Term[]>> hardCodedFacts = new HashMap<>();
		for (RelationSymbol sym : prog.getFactSymbols()) {
			hardCodedFacts.put(sym, new HashSet<>(prog.getFacts(sym)));
		}
		boolean ok = true;
		for (FormulogTest test : tests) {
			ok &= runTest(test, hardCodedFacts);
		}
		return ok;
	}

	private void clearCachedState() {
		// Need to clear memoized function calls
		prog.getFunctionCallFactory().clearMemoCache();
		// Need to reset predicate functions
		for (FunctionSymbol sym : prog.getFunctionSymbols()) {
			FunctionDef def = prog.getDef(sym);
			if (def instanceof DummyFunctionDef) {
				((DummyFunctionDef) def).setDef(null);
			}
		}
	}

	private boolean runTest(FormulogTest test, Map<RelationSymbol, Set<Term[]>> hardCodedFacts)
			throws InvalidProgramException, EvaluationException {
		for (RelationSymbol sym : prog.getFactSymbols()) {
			if (sym.isEdbSymbol()) {
				Set<Term[]> s = prog.getFacts(sym);
				s.clear();
				s.addAll(hardCodedFacts.get(sym));
				s.addAll(test.testInputs.get(sym));
			}
		}
		clearCachedState();
		// This would be better if we could set up the program, and then load
		// the external facts, so we do not need to do the setup each time.
		Evaluation e = SemiNaiveEvaluation.setup(prog, 1, false);
		System.out.print(test.name + "... ");
		e.run();
		List<String> errors = test.testLogic.apply(e.getResult());
		if (errors.isEmpty()) {
			System.out.println("PASSED");
			return true;
		} else {
			System.out.println("FAILED");
			for (String error : errors) {
				System.out.println(">>> " + error);
			}
			return false;
		}
	}

	private static class FormulogTest {
		public final String name;
		public final Map<RelationSymbol, Set<Term[]>> testInputs;
		public final Function<EvaluationResult, List<String>> testLogic;

		public FormulogTest(String name, Map<RelationSymbol, Set<Term[]>> testInputs,
				Function<EvaluationResult, List<String>> testLogic) {
			this.name = name;
			this.testInputs = testInputs;
			this.testLogic = testLogic;
		}
	}

	public static void main(String[] args) throws Exception {
		if (args.length != 1) {
			System.out.println("Expected a single Formulog file as an input.");
			System.exit(1);
		}
		if (Configuration.testFile == null) {
			System.out.println("Must specify a JSON test file.");
			System.exit(1);
		}
		main(new File(args[0]), new File(Configuration.testFile));
	}

	public static void main(File file, File json) throws Exception {
		FormulogTester tester = new FormulogTester();
		tester.setup(new FileReader(file), json);
		System.exit(tester.runTests() ? 0 : 1);
	}

}
