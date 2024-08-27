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
package edu.harvard.seas.pl.formulog.parsing;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TabSeparatedTermLineContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TsvFileContext;
import java.util.Set;

class FactFileParser {

  private final ParsingContext pc;

  public FactFileParser(ParsingContext parsingContext) {
    pc = parsingContext;
  }

  public void loadFacts(TsvFileContext ctx, int expectedArity, Set<Term[]> acc)
      throws ParseException {
    TermExtractor termExtractor = new TermExtractor(pc);
    VariableCheckPass varChecker = new VariableCheckPass(pc.symbolManager());
    for (TabSeparatedTermLineContext l : ctx.tabSeparatedTermLine()) {
      Term[] args = termExtractor.extractArray(l.term());
      if (args.length != expectedArity) {
        throw new ParseException(
            l.start.getLine(),
            "Arity mismatch: expected " + expectedArity + " terms, but got " + args.length);
      }
      try {
        args = varChecker.checkFact(args);
      } catch (VariableCheckPassException e) {
        throw new ParseException(l.start.getLine(), e.getMessage());
      }
      acc.add(args);
    }
  }
}
