package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
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

import java.io.PrintWriter;

import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.StringTerm;

public class BaseTerm implements CppExpr {

	private final Primitive<?> p;

	public static BaseTerm mk(Primitive<?> p) {
		return new BaseTerm(p);
	}
	
	private BaseTerm(Primitive<?> p) {
		this.p = p;
	}

	@Override
	public void print(PrintWriter out) {
		// XXX Need to handle special float values correctly
		out.print("Term::make(");
		if (p instanceof I32) {
			out.print("(int32_t) ");
		} else if (p instanceof I64) {
			out.print("(int64_t) ");
		} else if (p instanceof FP32) {
			out.print("(float) ");
		} else if (p instanceof FP64) {
			out.print("(double) ");
		} else if (p instanceof StringTerm) {
			// do nothing
		} else {
			throw new UnsupportedOperationException("Unsupported primitive: " + p);
		}
		out.print(p);
		out.print(")");
	}

}
