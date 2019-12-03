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

public class Lexer {

	private static final int BUF_CAPACITY = 1024;

	private final Reader reader;
	private final char[] buf = new char[BUF_CAPACITY];

	private int bufSize = BUF_CAPACITY;
	private int pos = BUF_CAPACITY;
	private int line = 1;
	private int column = 1;

	private TokenItem current = null;
	private TokenItem lookahead = null;

	private final boolean eolIsSignificant;

	public Lexer(Reader reader, boolean eolIsSignificant) throws IOException {
		this.reader = reader;
		this.eolIsSignificant = eolIsSignificant;
	}

	public boolean hasToken() throws IOException, LexingException {
		return load();
	}

	public boolean canPeek() throws IOException, LexingException {
		return loadLookAhead();
	}

	public TokenItem current() throws IOException, LexingException {
		if (!load()) {
			throw new NoSuchElementException("Tokenizer is exhausted.");
		}
		assert current != null;
		return current;
	}

	public TokenItem peek() throws IOException, LexingException {
		if (!loadLookAhead()) {
			throw new NoSuchElementException("Tokenizer is exhausted.");
		}
		assert current != null;
		assert lookahead != null;
		return lookahead;
	}

	public void step() throws IOException, LexingException {
		loadLookAhead();
		current = lookahead;
		lookahead = null;
	}

	private boolean load() throws IOException, LexingException {
		if (current == null) {
			current = loadToken();
		}
		return current != null;
	}

	private boolean loadLookAhead() throws IOException, LexingException {
		if (!load()) {
			throw new NoSuchElementException("Tokenizer is exhausted.");
		}
		if (lookahead == null) {
			lookahead = loadToken();
		}
		return lookahead != null;
	}

	private TokenItem loadToken() throws IOException, LexingException {
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
		if (ch == '(') return lparen();
		if (ch == ')') return rparen();
		if (Character.isLetter(ch)) return alphabetic();
		if (Character.isDigit(ch)) return number();
		
		throw new LexingException(
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
		String s = loadAlphanumeric();
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

	private TokenItem comma() {
		pos++;
		return TokenItem.mkComma(line, column++);
	}
	
	private TokenItem rparen() {
		pos++;
		return TokenItem.mkRightParen(line, column++);
	}
	
	private TokenItem lparen() throws IOException, LexingException {
		int start = column;
		pos++;
		column++;
		if (loadBuffer() && buf[pos] == '*') {
			comment(start);
			return loadToken();
		}
		return TokenItem.mkLeftParen(line, start);
	}

	private enum CommentState {
		SAW_STAR, SAW_LPAREN, SAW_NEITHER
	}
	
	private void comment(int start) throws IOException, LexingException {
		assert buf[pos] == '*';
		CommentState state = CommentState.SAW_NEITHER;
		int prevColumn;
		while (true) {
			pos++;
			prevColumn = column++;
			if (!loadBuffer()) {
				throw new LexingException("Unterminated comment (line " + line + ", column " + start + ")");
			}
			CommentState newState = CommentState.SAW_NEITHER;
			char ch = buf[pos];
			if (ch == '*') {
				if (state == CommentState.SAW_LPAREN) {
					comment(prevColumn);
				} else {
					newState = CommentState.SAW_STAR;
				}
			} else if (ch == '(') {
				newState = CommentState.SAW_LPAREN;
			} else if (ch == '\n') {
				lineFeed();
			} else if (ch == '\r') {
				carriageReturn();
			} else if (ch == ')' && state == CommentState.SAW_STAR) {
				break;
			}
			state = newState;
		}
		pos++;
		column++;
	}
	
	private TokenItem lineFeed() {
		pos++;
		int start = column;
		column = 1;
		return TokenItem.mkEol(line++, start);
	}

	private TokenItem period() throws IOException, LexingException {
		pos++;
		int start = column;
		column++;
		if (loadBuffer() && Character.isDigit(buf[pos])) {
			String num = "." + loadDigitString();
			String modifier = loadModifier();
			return number(num, NumberType.FP, modifier, start);
		}
		return TokenItem.mkPeriod(line, start);
	}

	private TokenItem semicolon() {
		pos++;
		return TokenItem.mkSemicolon(line, column++);
	}

	private static enum NumberType {
		INT, HEX, FP;
	}
	
	private TokenItem number() throws IOException, LexingException {
		int start = column;
		NumberType type = NumberType.INT;
		String num = loadDigitString();
		if (loadBuffer() && buf[pos] == '.') {
			type = NumberType.FP;
			pos++;
			column++;
			num += "." + loadDigitString();
		} else if (loadBuffer() && Character.toLowerCase(buf[pos]) == 'x' && num.equals("0")) {
			type = NumberType.HEX;
			pos++;
			column++;
			num = loadHexSuffix();
			if (num.equals("")) {
				throw new LexingException("Invalid hex literal (line " + line + ", column " + start + ")");
			}
		}
		String modifier = loadModifier();
		return number(num, type, modifier, start);
	}
	
	private TokenItem number(String num, NumberType type, String modifier, int start) throws IOException, LexingException {
		String modUpper = modifier.toUpperCase();
		int radix = type == NumberType.HEX ? 16 : 10;
		if (modUpper.equals("L") && type != NumberType.FP) {
			return TokenItem.mkLong(Long.parseUnsignedLong(num, radix), line, start);
		}
		if (modUpper.equals("F")) {
			return TokenItem.mkFloat(Float.parseFloat(num), line, start);
		}
		if (modUpper.equals("D")) {
			return TokenItem.mkDouble(Double.parseDouble(num), line, start);
		}
		if (modUpper.equals("E")) {
			if (!loadBuffer()) {
				throw new LexingException("Invalid number literal (line " + line + ", column " + start + ")");
			}
			String exp = "";
			if (buf[pos] == '-') {
				exp += "-";
				pos++;
				column++;
			}
			exp += loadDigitString();
			if (exp.equals("") || exp.equals("-")) {
				throw new LexingException("Invalid number literal (line " + line + ", column " + start + ")");
			}
			return TokenItem.mkDouble(Double.parseDouble(num + "e" + exp), line, start);
		}
		if (modUpper.equals("")) {
			if (type == NumberType.FP) {
				return TokenItem.mkDouble(Double.parseDouble(num), line, start);
			} else {
				return TokenItem.mkInt(Integer.parseUnsignedInt(num, radix), line, start);
			}
		}
		throw new LexingException(
				"Unrecognized modifier for number literal: " + modifier + " (line " + line + ", column " + start + ")");
	}
	
	private String loadDigitString() throws IOException {
		StringBuilder sb = new StringBuilder();
		char ch;
		while (loadBuffer() && Character.isDigit((ch = buf[pos]))) {
			sb.append(ch);
			pos++;
			column++;
		}
		return sb.toString();
	}
	
	private String loadHexSuffix() throws IOException {
		StringBuilder sb = new StringBuilder();
		char ch;
		while (loadBuffer() && (Character.isDigit((ch = Character.toUpperCase(buf[pos]))) || ch >= 'A' && ch <= 'F')) {
			sb.append(ch);
			pos++;
			column++;
		}
		return sb.toString();
	}
	
	private String loadModifier() throws IOException {
		char ch;
		while (loadBuffer() && Character.isLetter((ch = buf[pos]))) {
			pos++;
			column++;
			return Character.toString(ch);
		}
		return "";
	}

	private TokenItem string() throws IOException, LexingException {
		int start = column;
		char ch = buf[pos];
		assert ch == '"';
		StringBuilder sb = new StringBuilder();
		boolean escaped = false;
		while (true) {
			pos++;
			column++;
			boolean wasEscaped = escaped;
			escaped = false;
			if (!loadBuffer() || (ch = buf[pos]) == '\n' || ch == '\r') {
				throw new LexingException("Unterminated string (line " + line + ", column " + start + ")");
			}
			if (ch == '"' && !wasEscaped) {
				break;
			}
			if (ch == '\\') {
				escaped = !wasEscaped;
			}
			sb.append(ch);
		}
		pos++;
		column++;
		return TokenItem.mkString(sb.toString(), line, start);
	}

	private String loadAlphanumeric() throws IOException {
		StringBuilder sb = new StringBuilder();
		char ch;
		while (loadBuffer() && Character.isLetterOrDigit((ch = buf[pos]))) {
			sb.append(ch);
			pos++;
			column++;
		}
		return sb.toString();
	}

	public static void main(String[] args) throws IOException, LexingException {
		if (args.length != 1) {
			throw new IllegalArgumentException();
		}
		Reader reader = new FileReader(args[0]);
		reader = new StringReader("hello :-\r\ngoodbye. 1. 1f 2.0 .5f .5 1f 2l 3d 0xA 0xAl(* hello (* 1e3 *) 1e-3 *) 1e-4 ");
		Lexer t = new Lexer(reader, false);
		while (t.hasToken()) {
			System.out.println(t.current());
			t.step();
		}
	}

}
