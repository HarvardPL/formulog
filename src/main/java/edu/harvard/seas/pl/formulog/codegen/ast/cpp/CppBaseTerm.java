/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2022-2023 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.ast.BoolTerm;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import java.io.PrintWriter;

public class CppBaseTerm implements CppExpr {

  private final Primitive<?> p;

  public static CppBaseTerm mk(Primitive<?> p) {
    return new CppBaseTerm(p);
  }

  private CppBaseTerm(Primitive<?> p) {
    this.p = p;
  }

  @Override
  public void print(PrintWriter out) {
    String type;
    String val = p.toString();
    if (p instanceof I32) {
      type = "int32_t";
    } else if (p instanceof I64) {
      type = "int64_t";
    } else if (p instanceof FP32) {
      type = "float";
      val = handleFloat(((FP32) p).getVal());
    } else if (p instanceof FP64) {
      type = "double";
      val = handleDouble(((FP64) p).getVal());
    } else if (p instanceof BoolTerm) {
      type = "bool";
    } else if (p instanceof StringTerm) {
      type = "string";
    } else {
      throw new UnsupportedOperationException("Unsupported primitive: " + p);
    }
    printMakeTerm(type, val, out);
  }

  void printMakeTerm(String type, String val, PrintWriter out) {
    out.print("Term::make<");
    out.print(type);
    out.print(">(");
    out.print(val);
    out.print(")");
  }

  public static String handleDouble(double d) {
    if (d == Double.NEGATIVE_INFINITY) {
      return "-numeric_limits<double>::infinity()";
    } else if (d == Double.POSITIVE_INFINITY) {
      return "numeric_limits<double>::infinity()";
    } else if (Double.isNaN(d)) {
      return "nan(\"\")";
    } else {
      return Double.toString(d);
    }
  }

  public static String handleFloat(float d) {
    if (d == Float.NEGATIVE_INFINITY) {
      return "-numeric_limits<float>::infinity()";
    } else if (d == Float.POSITIVE_INFINITY) {
      return "numeric_limits<float>::infinity()";
    } else if (Float.isNaN(d)) {
      return "nanf(\"\")";
    } else {
      return Float.toString(d);
    }
  }
}
