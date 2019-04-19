package edu.harvard.seas.pl.formulog.smt;

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
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.IndexedSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;

public class SmtLibParser {

	private final SymbolManager symbolManager;
	private final Map<String, SolverVariable> variables;

	public SmtLibParser(SymbolManager symbolManager, Map<String, SolverVariable> variables) {
		this.symbolManager = symbolManager;
		this.variables = variables;
	}

	public Map<SolverVariable, Term> getModel(Reader r) throws IOException, SmtLibParseException {
		Tokenizer t = new Tokenizer(r);
		t.consume("(model");
		Map<SolverVariable, Term> m = new HashMap<>();
		while (!t.peek().equals(")")) {
			if (t.peek().equals(";")) {
				consumeComment(t);
			} else {
				parseFunctionDef(m, t);
			}
		}
		t.consume(")");
		return m;
	}
	
	private void consumeComment(Tokenizer t) throws IOException, SmtLibParseException {
		t.consume(";;");
		t.ignoreWhitespace(false);
		while (!t.next().equals("\n")) {
			// do nothing
		}
		t.ignoreWhitespace(true);
	}
	
	private void parseFunctionDef(Map<SolverVariable, Term> m, Tokenizer t) throws IOException, SmtLibParseException {
		t.consume("(");
		if (t.peek().equals("forall") || t.peek().equals("declare")) {
			skipRestOfSExp(t);
			return;
		}
		t.consume("define-fun");
		if (t.peek().equals("-")) {
			skipRestOfSExp(t);
			return;
		}
		String id = parseIdentifier(t);

		// Ignore args
		t.consume("(");
		skipRestOfSExp(t);

		// Parse type
		parseType(t);

		SolverVariable x = variables.get(id);
		if (x != null) {
			FunctorType ft = (FunctorType) x.getSymbol().getCompileTimeType();
			AlgebraicDataType type = (AlgebraicDataType) ft.getRetType();
			type = stripSymType(type);

			if (shouldRecord(type)) {
				m.put(x, parseTerm(t, type));
			}
		}
		skipRestOfSExp(t);
	}

	private static enum TermType {
		BV32, BV64, FP32, FP64, STRING, ADT
	}

	private AlgebraicDataType stripSymType(AlgebraicDataType symType) {
		assert symType.getSymbol().equals(BuiltInTypeSymbol.SYM_TYPE);
		return (AlgebraicDataType) symType.getTypeArgs().get(0);
	}

	private boolean shouldRecord(AlgebraicDataType type) {
		boolean ok = shouldRecord1(type);
		for (Type arg : type.getTypeArgs()) {
			if (arg instanceof AlgebraicDataType) {
				ok &= shouldRecord1((AlgebraicDataType) arg);
			}
		}
		return ok;
	}

	private boolean shouldRecord1(AlgebraicDataType type) {
		Symbol sym = type.getSymbol();
		if (sym instanceof IndexedSymbol) {
			switch ((IndexedSymbol) sym) {
			case BV: {
				TypeIndex idx = (TypeIndex) type.getTypeArgs().get(0);
				int w = idx.getIndex();
				return w == 32 || w == 64;
			}
			case FP: {
				TypeIndex idx1 = (TypeIndex) type.getTypeArgs().get(0);
				int e = idx1.getIndex();
				TypeIndex idx2 = (TypeIndex) type.getTypeArgs().get(1);
				int s = idx2.getIndex();
				return (e == 8 && s == 24) || (e == 11 && s == 53);
			}
			default:
				throw new AssertionError("impossible");
			}
		}
		if (sym instanceof BuiltInTypeSymbol) {
			switch ((BuiltInTypeSymbol) sym) {
			case BOOL_TYPE:
			case CMP_TYPE:
			case LIST_TYPE:
			case OPTION_TYPE:
			case STRING_TYPE:
				return true;
			case SMT_TYPE:
			case MODEL_TYPE:
			case SYM_TYPE:
			default:
				throw new AssertionError("impossible");
			}
		}
		return !sym.getSymbolType().equals(SymbolType.SOLVER_UNINTERPRETED_SORT);
	}

	private TermType getTermType(AlgebraicDataType type) {
		Symbol sym = type.getSymbol();
		if (sym instanceof IndexedSymbol) {
			switch ((IndexedSymbol) sym) {
			case BV: {
				TypeIndex idx = (TypeIndex) type.getTypeArgs().get(0);
				int w = idx.getIndex();
				if (w == 32) {
					return TermType.BV32;
				} else if (w == 64) {
					return TermType.BV64;
				}
				throw new AssertionError("impossible");
			}
			case FP: {
				TypeIndex idx1 = (TypeIndex) type.getTypeArgs().get(0);
				int e = idx1.getIndex();
				TypeIndex idx2 = (TypeIndex) type.getTypeArgs().get(1);
				int s = idx2.getIndex();
				if (e == 8 && s == 24) {
					return TermType.FP32;
				} else if (e == 11 && s == 53) {
					return TermType.FP64;
				}
				throw new AssertionError("impossible");
			}
			default:
				throw new AssertionError("impossible");
			}
		}
		if (sym instanceof BuiltInTypeSymbol) {
			switch ((BuiltInTypeSymbol) sym) {
			case BOOL_TYPE:
			case CMP_TYPE:
			case LIST_TYPE:
			case OPTION_TYPE:
				return TermType.ADT;
			case STRING_TYPE:
				return TermType.STRING;
			case SMT_TYPE:
			case MODEL_TYPE:
			case SYM_TYPE:
			default:
				throw new AssertionError("impossible");
			}
		}
		return TermType.ADT;
	}

	private String parseIdentifier(Tokenizer t) throws IOException, SmtLibParseException {
		String s = t.next();
		if (s.equals("|")) {
			s = "";
			while (!t.peek().equals("|")) {
				s += t.next();
			}
		} else {
			if (t.peek().equals("!")) {
				t.consume("!");
				s += "!";
				s += parseIdentifier(t);
			}
		}
		return s;
	}

	private void parseType(Tokenizer t) throws IOException, SmtLibParseException {
		String s = t.next();
		if (s.equals("(")) {
			skipRestOfSExp(t);
		}
	}

	private Term parseTerm(Tokenizer t, AlgebraicDataType type) throws IOException, SmtLibParseException {
		switch (getTermType(type)) {
		case ADT:
			return parseADTTerm(t, type);
		case BV32: {
			t.consume("#");
			String num = t.next().substring(1).toUpperCase();
			return I32.make(Integer.parseUnsignedInt(num, 16));
		}
		case BV64: {
			t.consume("#");
			String num = t.next().substring(1).toUpperCase();
			return I64.make(Long.parseUnsignedLong(num, 16));
		}
		// FIXME I'm not sure if these conversions to floating point are 100%
		// correct...
		case FP32: {
			float val = -1;
			t.consume("(");
			if (t.peek().equals("fp")) {
				t.consume("fp #");
				String sign = t.next().substring(1);
				t.consume("#");
				String exp = t.next().substring(1).toUpperCase();
				t.consume("#");
				String mant = t.next().substring(1);
				int bits = Integer.parseInt(sign) << 31;
				bits |= Integer.parseUnsignedInt(exp, 16) << 23;
				bits |= Integer.parseUnsignedInt(mant, 2);
				val = Float.intBitsToFloat(bits);
			} else {
				t.consume("_");
				String next = t.next();
				if (next.equals("NaN")) {
					val = Float.NaN;
				} else if (next.equals("+")) {
					if (t.peek().equals("oo")) {
						t.consume("oo");
						val = Float.POSITIVE_INFINITY;
					} else {
						t.consume("zero");
						val = +0.0f;
					}
				} else {
					assert next.equals("-");
					if (t.peek().equals("oo")) {
						t.consume("oo");
						val = Float.NEGATIVE_INFINITY;
					} else {
						t.consume("zero");
						val = -0.0f;
					}
				}
			}
			skipRestOfSExp(t);
			return FP32.make(val);
		}
		case FP64: {
			double val = -1;
			t.consume("(");
			if (t.peek().equals("fp")) {
				t.consume("fp #");
				String sign = t.next().substring(1);
				t.consume("#");
				String exp = t.next().substring(1);
				t.consume("#");
				String mant = t.next().substring(1).toUpperCase();
				long bits = Long.parseLong(sign) << 63;
				bits |= Long.parseUnsignedLong(exp, 2) << 52;
				bits |= Long.parseUnsignedLong(mant, 16);
				val = Double.longBitsToDouble(bits);
			} else {
				t.consume("_");
				String next = t.next();
				if (next.equals("NaN")) {
					val = Double.NaN;
				} else if (next.equals("+")) {
					if (t.peek().equals("oo")) {
						t.consume("oo");
						val = Double.POSITIVE_INFINITY;
					} else {
						t.consume("zero");
						val = +0.0;
					}
				} else {
					assert next.equals("-");
					if (t.peek().equals("oo")) {
						t.consume("oo");
						val = Double.NEGATIVE_INFINITY;
					} else {
						t.consume("zero");
						val = -0.0;
					}
				}
			}
			skipRestOfSExp(t);
			return FP64.make(val);
		}
		case STRING:
			return parseString(t);
		}
		throw new AssertionError("impossible");
	}

	// FIXME This is pretty rudimentary and doesn't capture a lot of cases (for
	// example, characters specified as hex codes).
	private Term parseString(Tokenizer t) throws IOException, SmtLibParseException {
		t.consume("\"");
		t.ignoreWhitespace(false);
		String s = "";
		loop: while (true) {
			String next = t.next();
			switch (next) {
			case "\"":
				// Z3 uses "" to represent "
				if (!t.peek().equals("\"")) {
					break loop;
				}
				t.consume("\"");
				s += "\\";
				// fall through
			default:
				s += next;
			}
		}
		t.ignoreWhitespace(true);
		return StringTerm.make(s);

	}

	private Term parseADTTerm(Tokenizer t, AlgebraicDataType type) throws IOException, SmtLibParseException {
		String id = t.next();
		if (id.equals("(")) {
			id = t.next();
			if (id.equals("as")) {
				Term term = parseADTTerm(t, type);
				skipRestOfSExp(t);
				return term;
			}
		}
		Symbol sym = symbolManager.lookupSymbol(id);
		Term[] args = Terms.emptyArray();
		if (sym.getArity() > 0) {
			List<Type> argTypes = null;
			for (ConstructorScheme cs : type.getConstructors()) {
				if (cs.getSymbol().equals(sym)) {
					argTypes = cs.getTypeArgs();
					break;
				}
			}
			assert argTypes != null;
			args = new Term[argTypes.size()];
			int i = 0;
			for (Type ty : argTypes) {
				Term arg = parseTerm(t, (AlgebraicDataType) ty);
				args[i] = arg;
				++i;
			}
			skipRestOfSExp(t);
		}
		return Constructors.make(sym, args);
	}

	private void skipRestOfSExp(Tokenizer t) throws IOException, SmtLibParseException {
		int depth = 0;
		while (depth >= 0) {
			switch (t.next()) {
			case "(":
				depth++;
				break;
			case ")":
				depth--;
				break;
			}
		}
	}

	private static class Tokenizer {

		private final StreamTokenizer t;

		public Tokenizer(Reader r) {
			t = new StreamTokenizer(r);
			t.ordinaryChar('.');
			t.ordinaryChar('-');
			t.ordinaryChars('0', '9');
			t.ordinaryChar('"');
			t.ordinaryChar('\'');
			t.wordChars('0', '9');
			t.wordChars('_', '_');
		}

		// FIXME This is almost certainly incomplete.
		public void ignoreWhitespace(boolean ignore) {
			if (ignore) {
				t.whitespaceChars('\n', '\n');
				t.whitespaceChars('\r', '\r');
				t.whitespaceChars('\t', '\t');
				t.whitespaceChars(' ', ' ');
			} else {
				t.ordinaryChar('\n');
				t.ordinaryChar('\r');
				t.ordinaryChar('\t');
				t.ordinaryChar(' ');
			}
		}

		public String peek() throws IOException, SmtLibParseException {
			String token = next();
			t.pushBack();
			return token;
		}

		public String next() throws IOException, SmtLibParseException {
			int token = t.nextToken();
			switch (t.ttype) {
			case StreamTokenizer.TT_EOF:
				throw new SmtLibParseException("Unexpected EOF.");
			case StreamTokenizer.TT_EOL:
				// This should only happen in the mode when whitespace is significant.
				return "\n";
			case StreamTokenizer.TT_NUMBER:
				throw new AssertionError("Nothing should be tokenized as a number.");
			case StreamTokenizer.TT_WORD:
				return t.sval;
			default:
				return Character.toString((char) token);
			}
		}

		public boolean hasNext() throws IOException {
			t.nextToken();
			t.pushBack();
			return t.ttype != StreamTokenizer.TT_EOF;
		}

		public void consume(String s) throws IOException, SmtLibParseException {
			Tokenizer t = new Tokenizer(new StringReader(s));
			while (t.hasNext()) {
				String expected = t.next();
				String found = next();
				if (!expected.equals(found)) {
					throw new SmtLibParseException(
							"Tried to consume \"" + expected + "\", but found \"" + found + "\".");
				}
			}
		}

	}

	@SuppressWarnings("serial")
	public static class SmtLibParseException extends Exception {

		public SmtLibParseException(String message) {
			super(message);
		}

	}

}
