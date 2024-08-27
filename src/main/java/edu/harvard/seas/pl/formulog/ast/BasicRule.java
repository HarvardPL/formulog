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
package edu.harvard.seas.pl.formulog.ast;

import java.util.Collections;
import java.util.List;

public class BasicRule extends AbstractRule<UserPredicate, ComplexLiteral> {

  private BasicRule(UserPredicate head, List<ComplexLiteral> body) {
    super(head, body);
    if (!head.getSymbol().isIdbSymbol()) {
      throw new IllegalArgumentException(
          "Cannot create rule with non-IDB predicate for head: " + head.getSymbol());
    }
  }

  public static BasicRule make(UserPredicate head, List<ComplexLiteral> body) {
    if (body.isEmpty()) {
      return make(head);
    }
    return new BasicRule(head, body);
  }

  public static BasicRule make(UserPredicate head) {
    return make(head, Collections.singletonList(ComplexLiterals.trueAtom()));
  }
}
