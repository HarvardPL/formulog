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
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationResult;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.TypeException;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.sexp.SExp;
import edu.harvard.seas.pl.formulog.util.sexp.SExpException;
import edu.harvard.seas.pl.formulog.util.sexp.SExpParser;

public class FormulogTester {

	/*
	 * How this is going to work: - Get a program and JSON file - Parse (with no
	 * external directories) and type check program - Get initial facts; these will
	 * be the same in each test - Then loop through tests in JSON file, extracting
	 * new facts as necessary - Will need to update pc in Parser to be an instance
	 * field - Parser will also need a parseExternalFacts(RelationSymbol) method
	 */

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
			if (sym.isEdbSymbol() && sym.isExternal()) {
				FileReader fr = new FileReader(dir.resolve(sym + ".tsv").toFile());
				Set<Term[]> s = parser.parseFacts(sym, fr);
				m.put(sym, s);
			}
		}
		try {
			Function<EvaluationResult, Optional<String>> logic = parseBoolLogic(test.get("logic").asText());
			return new FormulogTest(name, m, logic);
		} catch (ParseException e) {
			throw new ParseException(-1, "Trouble parsing logic for test " + name + ": " + e.getMessage());
		}
	}

	private Function<EvaluationResult, Optional<String>> parseBoolLogic(String s) throws ParseException {
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

	private Function<EvaluationResult, Optional<String>> parseBoolLogic(SExp sexp) throws ParseException {
		if (sexp.isAtom()) {
			return parseBoolAtom(sexp.asAtom());
		} else {
			return parseBoolList(sexp.asList());
		}
	}

	private Function<EvaluationResult, Optional<String>> parseBoolAtom(String atom) throws ParseException {
		switch (atom) {
		case "true":
			return r -> Optional.empty();
		default:
			throw new ParseException(-1, "Unrecognized boolean constant: " + atom);
		}
	}

	private Function<EvaluationResult, Optional<String>> parseBoolList(List<SExp> l) throws ParseException {
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
					return Optional.empty();
				} else {
					return Optional.of(
							"Failed equality: " + sexp1 + " has value " + v1 + ", but " + sexp2 + " has value " + v2);
				}
			};
		}
		case "and": {
			List<Function<EvaluationResult, Optional<String>>> fs = new ArrayList<>();
			for (Iterator<SExp> it = l.listIterator(1); it.hasNext();) {
				fs.add(parseBoolLogic(it.next()));
			}
			return r -> {
				String s = "";
				for (Function<EvaluationResult, Optional<String>> f : fs) {
					Optional<String> o = f.apply(r);
					if (o.isPresent()) {
						if (!s.isEmpty()) {
							s += "\n";
						}
						s += o.get();
					}
				}
				if (s.isEmpty()) {
					return Optional.empty();
				} else {
					return Optional.of(s);
				}
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
			SExp sexp1 = l.get(0);
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

	synchronized void runTests() {
		if (!initialized) {
			throw new IllegalStateException("Need to set up tests first.");
		}
	}

	private static class FormulogTest {
		public final String name;
		public final Map<RelationSymbol, Set<Term[]>> testInputs;
		public final Function<EvaluationResult, Optional<String>> testLogic;

		public FormulogTest(String name, Map<RelationSymbol, Set<Term[]>> testInputs,
				Function<EvaluationResult, Optional<String>> testLogic) {
			this.name = name;
			this.testInputs = testInputs;
			this.testLogic = testLogic;
		}
	}

}
