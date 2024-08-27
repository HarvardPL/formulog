/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2021-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.util.sexp;

import java.io.Reader;
import java.io.StringReader;

public class SExpLexer {

  private static final int BUF_CAPACITY = 1024;
  private char[] buf = new char[BUF_CAPACITY];
  private int pos = 0;
  private int bufSize = 0;

  private boolean ready;
  private SExpToken curToken;
  private String curValue;

  private final Reader reader;

  public SExpLexer(Reader reader) {
    this.reader = reader;
  }

  public SExpToken curToken() throws SExpException {
    if (!ready && !loadNextToken()) {
      throw new SExpException("No more tokens");
    }
    return curToken;
  }

  public String curValue() throws SExpException {
    if (!ready && !loadNextToken()) {
      throw new SExpException("No more tokens");
    }
    if (curValue == null) {
      throw new SExpException("No value associated with current token");
    }
    return curValue;
  }

  public void step() throws SExpException {
    if (!ready) {
      loadNextToken();
    }
    ready = false;
  }

  public boolean hasToken() throws SExpException {
    return ready || loadNextToken();
  }

  public void consume(SExpToken token) throws SExpException {
    SExpToken got = curToken();
    if (got == token) {
      step();
    } else {
      throw new SExpException("Expected " + token + " but got " + got);
    }
  }

  private boolean loadNextToken() throws SExpException {
    curToken = null;
    curValue = null;
    while (load() && Character.isWhitespace(buf[pos])) {
      pos++;
    }
    if (!load()) {
      return false;
    }
    char ch = buf[pos];
    switch (ch) {
      case '(':
        curToken = SExpToken.LPAREN;
        pos++;
        break;
      case ')':
        curToken = SExpToken.RPAREN;
        pos++;
        break;
      default:
        curToken = SExpToken.ATOM;
        curValue = readAtom();
    }
    ready = true;
    return true;
  }

  private String readAtom() throws SExpException {
    StringBuilder sb = new StringBuilder();
    char ch;
    while (load() && (ch = buf[pos]) != ')' && ch != '(' && !Character.isWhitespace(ch)) {
      sb.append(ch);
      pos++;
    }
    return sb.toString();
  }

  private boolean load() throws SExpException {
    if (pos >= bufSize) {
      try {
        bufSize = reader.read(buf);
      } catch (Exception e) {
        throw new SExpException(e);
      }
      pos = 0;
    }
    return bufSize > 0;
  }

  public static void main(String[] args) throws SExpException {
    Reader r = new StringReader("(hello 2(x ()) )");
    SExpLexer lexer = new SExpLexer(r);
    while (lexer.hasToken()) {
      switch (lexer.curToken) {
        case ATOM:
          System.out.println(lexer.curValue());
          break;
        case LPAREN:
          System.out.println("(");
          break;
        case RPAREN:
          System.out.println(")");
          break;
      }
      lexer.step();
    }
  }
}
