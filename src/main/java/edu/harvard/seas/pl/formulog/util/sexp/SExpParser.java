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
import java.util.ArrayList;
import java.util.List;

public class SExpParser {

  private final SExpLexer lexer;

  public SExpParser(Reader r) {
    lexer = new SExpLexer(r);
  }

  public SExp parse() throws SExpException {
    switch (lexer.curToken()) {
      case ATOM:
        SExp atom = new SExpAtom(lexer.curValue());
        lexer.step();
        return atom;
      case LPAREN:
        return parseList();
      case RPAREN:
        throw new SExpException("Unexpected right parenthesis");
      default:
        throw new AssertionError("Impossible");
    }
  }

  private SExp parseList() throws SExpException {
    lexer.consume(SExpToken.LPAREN);
    List<SExp> l = new ArrayList<>();
    boolean go = true;
    while (go) {
      switch (lexer.curToken()) {
        case ATOM:
          l.add(new SExpAtom(lexer.curValue()));
          lexer.step();
          break;
        case LPAREN:
          l.add(parseList());
          break;
        case RPAREN:
          go = false;
          break;
      }
    }
    lexer.consume(SExpToken.RPAREN);
    return new SExpList(l);
  }

  public static void main(String[] args) throws SExpException {
    Reader r = new StringReader("(hello 2(x ()) )");
    SExpParser parser = new SExpParser(r);
    System.out.println(parser.parse());
  }
}
