package edu.harvard.seas.pl.formulog.parsing;

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

import java.io.IOException;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.util.Pair;

public class NewParser {

	private final SymbolManager symbolManager = new SymbolManager();

	public Pair<BasicProgram, Set<RelationSymbol>> parseProgram(Lexer lexer)
			throws IOException, LexingException, ParseException {
		return new ProgramParser(lexer).run();
	}

	public Term[] parseTabSeparatedTerms(Lexer lexer) {
		if (!lexer.eolIsSignificant()) {
			throw new IllegalArgumentException("Lexer must treat EOL as significant.");
		}
		return null;
	}

	private class ProgramParser {

		private final Lexer lexer;
		private final Map<RelationSymbol, Set<Term[]>> facts = new ConcurrentHashMap<>();
		private final Map<RelationSymbol, Set<BasicRule>> rules = new ConcurrentHashMap<>();

		public ProgramParser(Lexer lexer) {
			this.lexer = lexer;
		}

		private Pair<BasicProgram, Set<RelationSymbol>> run() throws IOException, LexingException, ParseException {
			while (lexer.hasToken()) {
				toplevel();
			}
			return null;
		}

		private void toplevel() throws IOException, LexingException, ParseException {
			while (lexer.hasToken()) {
				TokenItem t = lexer.current();
				switch (t.token) {
				case AT_ID:
				case INPUT:
				case OUTPUT:
					parseRelationDeclaration();
					break;
				case FUN:
				case ID:
				default:
					badToken(t);
				}
			}
		}

		private void parseRelationDeclaration() throws IOException, LexingException, ParseException {
			TokenItem t = lexer.current();
			TokenItem annotation = null;
			if (t.token == Token.AT_ID) {
				annotation = t;
				t = lexer.step();
			}
			boolean isInput;
			switch (t.token) {
			case INPUT:
				isInput = true;
				break;
			case OUTPUT:
				isInput = false;
				break;
			default:
				badToken(t);
			}
			
			t = lexer.step();
			if (t.token != Token.ID) {
				badToken(t);
			}
			String name = (String) t.value;
			
		}

	}
	
	private void badToken(TokenItem t) throws ParseException {
		throw new ParseException("Unexpected token: " + t.token + " (line " + t.line + ", " + t.column + ")");
	}

}
