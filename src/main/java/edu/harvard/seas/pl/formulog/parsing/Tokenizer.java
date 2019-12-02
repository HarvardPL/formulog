package edu.harvard.seas.pl.formulog.parsing;

import java.io.FileReader;

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
import java.io.Reader;
import java.io.StringReader;
import java.util.NoSuchElementException;

public class Tokenizer {

	private static final int BUF_CAPACITY = 1024;

	private final Reader reader;
	private final char[] buf = new char[BUF_CAPACITY];

	private int bufSize = BUF_CAPACITY;
	private int pos = BUF_CAPACITY;
	private int line = 1;
	private int column = 1;

	private TokenItem curTokenItem = null;
	private TokenItem peekTokenItem = null;

	private boolean eolIsSignificant = false;

	public Tokenizer(Reader reader) throws IOException {
		this.reader = reader;
	}

	public void eolIsSignificant(boolean isSignificant) {
		eolIsSignificant = isSignificant;
	}

	public boolean hasToken() throws IOException, UnrecognizedTokenException {
		return load();
	}

	public boolean canPeek() throws IOException, UnrecognizedTokenException {
		return loadLookAhead();
	}

	public TokenItem current() throws IOException, UnrecognizedTokenException {
		if (!load()) {
			throw new NoSuchElementException("Tokenizer is exhausted.");
		}
		assert curTokenItem != null;
		return curTokenItem;
	}

	public TokenItem peek() throws IOException, UnrecognizedTokenException {
		if (!loadLookAhead()) {
			throw new NoSuchElementException("Tokenizer is exhausted.");
		}
		assert curTokenItem != null;
		assert peekTokenItem != null;
		return peekTokenItem;
	}

	public void step() throws IOException, UnrecognizedTokenException {
		loadLookAhead();
		curTokenItem = peekTokenItem;
		peekTokenItem = null;
	}

	private boolean load() throws IOException, UnrecognizedTokenException {
		if (curTokenItem == null) {
			curTokenItem = loadToken();
		}
		return curTokenItem != null;
	}

	private boolean loadLookAhead() throws IOException, UnrecognizedTokenException {
		if (!load()) {
			throw new NoSuchElementException("Tokenizer is exhausted.");
		}
		if (peekTokenItem == null) {
			peekTokenItem = loadToken();
		}
		return peekTokenItem != null;
	}

	private TokenItem loadToken() throws IOException, UnrecognizedTokenException {
		char ch;
		boolean skipNextLineFeed = false;
		while (loadBuffer() && (Character.isWhitespace((ch = buf[pos])))) {
			if (ch == '\n') {
				if (eolIsSignificant) {
					break;
				}
				if (!skipNextLineFeed) {
					line++;
					column = 1;
				}
				skipNextLineFeed = false;
			} else if (ch == '\r') {
				if (eolIsSignificant) {
					break;
				}
				line++;
				column = 1;
				skipNextLineFeed = true;
			} else {
				column++;
				skipNextLineFeed = false;
			}
			pos++;
		}
		if (!loadBuffer()) {
			return null;
		}

		ch = buf[pos];
		if (ch == '"') return string();
		if (ch == '.') return period();
		if (ch == ':') return colon();
		if (ch == ',') return comma();
		if (ch == ';') return semicolon();
		if (ch == '\n') return lineFeed();
		if (ch == '\r') return carriageReturn();
		if (Character.isLetter(ch)) return alphabetic();
		if (Character.isDigit(ch)) return number();
		
		throw new UnrecognizedTokenException(
				"Unrecognized character: " + ch + " (line " + line + ", column " + column + ")");
	}

	private boolean loadBuffer() throws IOException {
		if (pos == bufSize) {
			int size = reader.read(buf);
			if (size < 0) {
				size = 0;
			}
			pos = 0;
			bufSize = size;
			return bufSize != 0;
		}
		return true;
	}

	private TokenItem alphabetic() throws IOException {
		int start = column;
		String s = loadAlphaNumeric();
		switch (s) {
		case "fun":
			return TokenItem.mkFun(line, start);
		case "input":
			return TokenItem.mkInput(line, start);
		case "output":
			return TokenItem.mkOutput(line, start);
		default:
			return TokenItem.mkId(s, line, start);
		}
	}
	
	private TokenItem carriageReturn() throws IOException {
		int start = column;
		pos++;
		column = 1;
		if (loadBuffer() && buf[pos] == '\n') {
			pos++;
		}
		return TokenItem.mkEol(line++, start);
	}

	private TokenItem colon() throws IOException {
		int start = column;
		pos++;
		column++;
		if (loadBuffer() && buf[pos] == '-') {
			pos++;
			column++;
			return TokenItem.mkTurnstile(line, start);
		}
		return TokenItem.mkColon(line, start);
	}

	private TokenItem comma() throws IOException {
		pos++;
		return TokenItem.mkComma(line, column++);
	}
	
	private TokenItem lineFeed() throws IOException {
		pos++;
		int start = column;
		column = 1;
		return TokenItem.mkEol(line++, start);
	}

	private TokenItem period() throws IOException {
		pos++;
		return TokenItem.mkPeriod(line, column++);
	}

	private TokenItem semicolon() throws IOException {
		pos++;
		return TokenItem.mkSemicolon(line, column++);
	}

	private TokenItem number() {
		throw new UnsupportedOperationException();
	}

	private TokenItem string() {
		throw new UnsupportedOperationException();
	}

	private String loadAlphaNumeric() throws IOException {
		StringBuilder sb = new StringBuilder();
		char ch;
		while (loadBuffer() && Character.isLetterOrDigit((ch = buf[pos]))) {
			sb.append(ch);
			pos++;
			column++;
		}
		return sb.toString();
	}

	public static void main(String[] args) throws IOException, UnrecognizedTokenException {
		if (args.length != 1) {
			throw new IllegalArgumentException();
		}
		Reader reader = new FileReader(args[0]);
		reader = new StringReader("hello :-\r\ngoodbye.");
		Tokenizer t = new Tokenizer(reader);
		t.eolIsSignificant(false);
		while (t.hasToken()) {
			System.out.println(t.current());
			t.step();
		}
	}

}
