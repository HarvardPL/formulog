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

import edu.harvard.seas.pl.formulog.codegen.CodeGenUtil;
import java.io.PrintWriter;

public class CppReturn implements CppStmt {

  private final CppExpr val;

  private CppReturn(CppExpr val) {
    this.val = val;
  }

  public static CppReturn mk(CppExpr val) {
    return new CppReturn(val);
  }

  public static CppReturn mk() {
    return new CppReturn(null);
  }

  @Override
  public void println(PrintWriter out, int indent) {
    CodeGenUtil.printIndent(out, indent);
    if (val == null) {
      out.println("return;");
      return;
    }
    out.print("return ");
    val.print(out);
    out.println(";");
  }
}
