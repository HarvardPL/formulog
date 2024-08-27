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
package edu.harvard.seas.pl.formulog.codegen.ast.cpp;

import java.io.PrintWriter;

public class CppCast implements CppExpr {

  private final String type;
  private final CppExpr expr;
  private final String castName;

  private CppCast(String castName, String type, CppExpr expr) {
    this.type = type;
    this.expr = expr;
    this.castName = castName;
  }

  public static CppCast mkReinterpret(String type, CppExpr expr) {
    return new CppCast("reinterpret_cast", type, expr);
  }

  @Override
  public void print(PrintWriter out) {
    out.print(castName);
    out.print("<");
    out.print(type);
    out.print(">");
    out.print("(");
    expr.print(out);
    out.print(")");
  }
}
