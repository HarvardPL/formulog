package edu.harvard.seas.pl.formulog.functions;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.harvard.seas.pl.formulog.ast.Constructors;

/*-
 * #%L
 * Formulog
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

import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;

public final class PrimitiveConversions {

	private PrimitiveConversions() {
		throw new AssertionError();
	}

	public static final FunctionDef i32ToI64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.i32ToI64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 x = (I32) args[0];
			return I64.make(x.getVal());
		}

	};

	public static final FunctionDef i32ToFp32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.i32ToFp32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 x = (I32) args[0];
			return FP32.make(x.getVal());
		}

	};

	public static final FunctionDef i32ToFp64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.i32ToFp64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 x = (I32) args[0];
			return FP64.make(x.getVal());
		}

	};

	public static final FunctionDef i64ToI32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.i64ToI32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 x = (I64) args[0];
			return I32.make(x.getVal().intValue());
		}

	};

	public static final FunctionDef i64ToFp32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.i64ToFp32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 x = (I64) args[0];
			return FP32.make(x.getVal());
		}

	};

	public static final FunctionDef i64ToFp64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.i64ToFp64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 x = (I64) args[0];
			return FP64.make(x.getVal());
		}

	};

	public static final FunctionDef fp32ToI32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.fp32ToI32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 x = (FP32) args[0];
			return I32.make(x.getVal().intValue());
		}

	};

	public static final FunctionDef fp32ToI64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.fp32ToI64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 x = (FP32) args[0];
			return I64.make(x.getVal().longValue());
		}

	};

	public static final FunctionDef fp32ToFp64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.fp32ToFp64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 x = (FP32) args[0];
			return FP64.make(x.getVal());
		}

	};

	public static final FunctionDef fp64ToI32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.fp64ToI32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 x = (FP64) args[0];
			return I32.make(x.getVal().intValue());
		}

	};

	public static final FunctionDef fp64ToI64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.fp64ToI64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 x = (FP64) args[0];
			return I64.make(x.getVal().longValue());
		}

	};

	public static final FunctionDef fp64ToFp32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.fp64ToFp32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 x = (FP64) args[0];
			return FP32.make(x.getVal().floatValue());
		}

	};

	private static final Pattern hex = Pattern.compile("0x([0-9a-fA-F]+)");

	public static final FunctionDef stringToI32 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.stringToI32;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			try {
				String s = ((StringTerm) args[0]).getVal();
				Matcher m = hex.matcher(s);
				Integer i;
				if (m.matches()) {
					i = Integer.parseUnsignedInt(m.group(1), 16);
				} else {
					i = Integer.parseInt(s);
				}
				return Constructors.some(I32.make(i));
			} catch (NumberFormatException e) {
				return Constructors.none();
			}
		}

	};

	public static final FunctionDef stringToI64 = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.stringToI64;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			try {
				String s = ((StringTerm) args[0]).getVal();
				Matcher m = hex.matcher(s);
				Long i;
				if (m.matches()) {
					i = Long.parseUnsignedLong(m.group(1), 16);
				} else {
					i = Long.parseLong(s);
				}
				return Constructors.some(I64.make(i));
			} catch (NumberFormatException e) {
				return Constructors.none();
			}
		}

	};

}
