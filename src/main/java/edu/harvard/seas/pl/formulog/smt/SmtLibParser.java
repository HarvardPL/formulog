/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2019-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.smt;

import edu.harvard.seas.pl.formulog.ast.BoolTerm;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import java.io.IOException;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SmtLibParser {

  private final SymbolManager symbolManager;
  private final Map<String, SolverVariable> variables;

  public SmtLibParser(SymbolManager symbolManager, Map<String, SolverVariable> variables) {
    this.symbolManager = symbolManager;
    this.variables = variables;
  }

  public Map<SolverVariable, Term> getModel(Reader r) throws IOException, SmtLibParseException {
    Tokenizer t = new Tokenizer(r);
    t.consume("(");
    Map<SolverVariable, Term> m = new HashMap<>();
    while (!t.peek().equals(")")) {
      if (t.peek().equals(";")) {
        consumeComment(t);
      } else {
        parseFunctionDef(m, t);
      }
    }
    t.consume(")");
    t.ignoreWhitespace(false);
    // Remove EOL
    t.next();
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

  private void parseFunctionDef(Map<SolverVariable, Term> m, Tokenizer t)
      throws IOException, SmtLibParseException {
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
    BV32,
    BV64,
    FP32,
    FP64,
    STRING,
    ADT
  }

  public static AlgebraicDataType stripSymType(AlgebraicDataType symType) {
    assert symType.getSymbol().equals(BuiltInTypeSymbol.SYM_TYPE);
    return (AlgebraicDataType) symType.getTypeArgs().get(0);
  }

  public static boolean shouldRecord(AlgebraicDataType type) throws SmtLibParseException {
    Set<Symbol> seen = new HashSet<>();
    boolean ok = shouldRecord1(type, seen);
    for (Type arg : type.getTypeArgs()) {
      if (arg instanceof AlgebraicDataType) {
        ok &= shouldRecord1((AlgebraicDataType) arg, seen);
      }
    }
    return ok;
  }

  private static void die(String msg) throws SmtLibParseException {
    throw new SmtLibParseException("INTERNAL ERROR: " + msg);
  }

  private static boolean shouldRecord1(AlgebraicDataType type, Set<Symbol> seen)
      throws SmtLibParseException {
    TypeSymbol sym = type.getSymbol();
    if (!seen.add(sym)) {
      return true;
    }
    if (sym instanceof BuiltInTypeSymbol) {
      switch ((BuiltInTypeSymbol) sym) {
        case BOOL_TYPE:
        case CMP_TYPE:
        case LIST_TYPE:
        case OPTION_TYPE:
        case STRING_TYPE:
          return true;
        case ARRAY_TYPE:
        case INT_TYPE:
          return false;
        case BV:
          TypeIndex idx = (TypeIndex) type.getTypeArgs().get(0);
          int w = idx.getIndex();
          return w == 32 || w == 64;
        case FP:
          TypeIndex idx1 = (TypeIndex) type.getTypeArgs().get(0);
          int e = idx1.getIndex();
          TypeIndex idx2 = (TypeIndex) type.getTypeArgs().get(1);
          int s = idx2.getIndex();
          return (e == 8 && s == 24) || (e == 11 && s == 53);
        case SMT_TYPE:
        case MODEL_TYPE:
        case SYM_TYPE:
        default:
          die("unexpected built-in symbol: " + sym);
      }
    }
    if (sym.isUninterpretedSort()) {
      return false;
    }
    boolean ok = true;
    if (type.hasConstructors()) {
      for (ConstructorScheme cs : type.getConstructors()) {
        for (Type ty : cs.getTypeArgs()) {
          if (ty instanceof AlgebraicDataType) {
            ok &= shouldRecord1((AlgebraicDataType) ty, seen);
          }
        }
      }
    }
    return ok;
  }

  private TermType getTermType(AlgebraicDataType type) throws SmtLibParseException {
    TypeSymbol sym = type.getSymbol();
    if (sym instanceof BuiltInTypeSymbol) {
      switch ((BuiltInTypeSymbol) sym) {
        case BOOL_TYPE:
        case CMP_TYPE:
        case LIST_TYPE:
        case OPTION_TYPE:
          return TermType.ADT;
        case STRING_TYPE:
          return TermType.STRING;
        case BV:
          {
            TypeIndex idx = (TypeIndex) type.getTypeArgs().get(0);
            int w = idx.getIndex();
            if (w == 32) {
              return TermType.BV32;
            } else if (w == 64) {
              return TermType.BV64;
            }
            die("unexpected BV width " + w);
          }
        case FP:
          {
            TypeIndex idx1 = (TypeIndex) type.getTypeArgs().get(0);
            int e = idx1.getIndex();
            TypeIndex idx2 = (TypeIndex) type.getTypeArgs().get(1);
            int s = idx2.getIndex();
            if (e == 8 && s == 24) {
              return TermType.FP32;
            } else if (e == 11 && s == 53) {
              return TermType.FP64;
            }
            die("unexpected FP dimensions " + e + "/" + s);
          }
        default:
          die("unexpected built-in symbol: " + sym);
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

  private long parseBv(Tokenizer t) throws IOException, SmtLibParseException {
    t.consume("#");
    String tok = t.next();
    String prefix = tok.substring(0, 1);
    String num = tok.substring(1);
    int base = 0;
    if (prefix.equals("b")) {
      base = 2;
    } else {
      assert (prefix.equals("x"));
      base = 16;
    }
    return Long.parseUnsignedLong(num, base);
  }

  private Term parseTerm(Tokenizer t, AlgebraicDataType type)
      throws IOException, SmtLibParseException {
    switch (getTermType(type)) {
      case ADT:
        return parseADTTerm(t, type);
      case BV32:
        {
          return I32.make((int) parseBv(t));
        }
      case BV64:
        {
          return I64.make(parseBv(t));
        }
      // FIXME I'm not sure if these conversions to floating point are 100%
      // correct...
      case FP32:
        {
          float val = -1;
          t.consume("(");
          if (t.peek().equals("fp")) {
            t.consume("fp");
            long sign = parseBv(t);
            long exp = parseBv(t);
            long mant = parseBv(t);
            long bits = sign << 31;
            bits |= exp << 23;
            bits |= mant;
            val = Float.intBitsToFloat((int) bits);
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
      case FP64:
        {
          double val = -1;
          t.consume("(");
          if (t.peek().equals("fp")) {
            t.consume("fp");
            long sign = parseBv(t);
            long exp = parseBv(t);
            long mant = parseBv(t);
            long bits = sign << 63;
            bits |= exp << 52;
            bits |= mant;
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
    die("unexpected term type: " + getTermType(type));
    return null;
  }

  private Term parseString(Tokenizer t) throws IOException, SmtLibParseException {
    t.consume("\"");
    t.ignoreWhitespace(false);
    StringBuilder sb = new StringBuilder();
    while (true) {
      String next = t.next();
      if (next.equals("\"")) {
        // SMT-LIB uses "" to represent the character "
        if (!t.peek().equals("\"")) {
          break;
        }
        t.consume("\"");
      }
      sb.append(next);
    }
    t.ignoreWhitespace(true);
    return StringTerm.make(sb.toString());
  }

  private Term parseADTTerm(Tokenizer t, AlgebraicDataType type)
      throws IOException, SmtLibParseException {
    String id = t.next();
    if (id.equals("(")) {
      id = t.next();
      if (id.equals("as")) {
        Term term = parseADTTerm(t, type);
        skipRestOfSExp(t);
        return term;
      }
    }
    if (id.equals("true")) {
      return BoolTerm.mkTrue();
    }
    if (id.equals("false")) {
      return BoolTerm.mkFalse();
    }
    ConstructorSymbol sym = (ConstructorSymbol) symbolManager.lookupSymbol(id);
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
      t.ordinaryChar('/');
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
          die("nothing should be tokenized as a number.");
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
