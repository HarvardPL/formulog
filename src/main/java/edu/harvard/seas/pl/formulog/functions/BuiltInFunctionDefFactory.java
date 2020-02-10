package edu.harvard.seas.pl.formulog.functions;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.function.BiFunction;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

import org.pcollections.HashTreePMap;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BoolTerm;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.Model;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.smt.SmtManager;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Triple;

public final class BuiltInFunctionDefFactory {

	private final SmtManager smt;

	public BuiltInFunctionDefFactory(SmtManager smt) {
		this.smt = smt;
	}

	public FunctionDef get(BuiltInFunctionSymbol sym) {
		switch (sym) {
		case I32_ADD:
			return I32Add.INSTANCE;
		case I32_SUB:
			return I32Sub.INSTANCE;
		case I32_MUL:
			return I32Mul.INSTANCE;
		case I32_DIV:
			return I32Div.INSTANCE;
		case I32_REM:
			return I32Rem.INSTANCE;
		case I32_NEG:
			return I32Neg.INSTANCE;
		case I32_AND:
			return I32And.INSTANCE;
		case I32_OR:
			return I32Or.INSTANCE;
		case I32_XOR:
			return I32Xor.INSTANCE;
		case I32_GT:
			return I32Gt.INSTANCE;
		case I32_GE:
			return I32Gte.INSTANCE;
		case I32_LT:
			return I32Lt.INSTANCE;
		case I32_LE:
			return I32Lte.INSTANCE;
		case I64_ADD:
			return I64Add.INSTANCE;
		case I64_SUB:
			return I64Sub.INSTANCE;
		case I64_MUL:
			return I64Mul.INSTANCE;
		case I64_DIV:
			return I64Div.INSTANCE;
		case I64_REM:
			return I64Rem.INSTANCE;
		case I64_NEG:
			return I64Neg.INSTANCE;
		case I64_AND:
			return I64And.INSTANCE;
		case I64_OR:
			return I64Or.INSTANCE;
		case I64_XOR:
			return I64Xor.INSTANCE;
		case I64_GT:
			return I64Gt.INSTANCE;
		case I64_GE:
			return I64Gte.INSTANCE;
		case I64_LT:
			return I64Lt.INSTANCE;
		case I64_LE:
			return I64Lte.INSTANCE;
		case FP32_ADD:
			return FP32Add.INSTANCE;
		case FP32_SUB:
			return FP32Sub.INSTANCE;
		case FP32_MUL:
			return FP32Mul.INSTANCE;
		case FP32_DIV:
			return FP32Div.INSTANCE;
		case FP32_REM:
			return FP32Rem.INSTANCE;
		case FP32_NEG:
			return FP32Neg.INSTANCE;
		case FP32_GT:
			return FP32Gt.INSTANCE;
		case FP32_GE:
			return FP32Gte.INSTANCE;
		case FP32_LT:
			return FP32Lt.INSTANCE;
		case FP32_LE:
			return FP32Lte.INSTANCE;
		case FP32_EQ:
			return FP32Eq.INSTANCE;
		case FP64_ADD:
			return FP64Add.INSTANCE;
		case FP64_SUB:
			return FP64Sub.INSTANCE;
		case FP64_MUL:
			return FP64Mul.INSTANCE;
		case FP64_DIV:
			return FP64Div.INSTANCE;
		case FP64_REM:
			return FP64Rem.INSTANCE;
		case FP64_NEG:
			return FP64Neg.INSTANCE;
		case FP64_GT:
			return FP64Gt.INSTANCE;
		case FP64_GE:
			return FP64Gte.INSTANCE;
		case FP64_LT:
			return FP64Lt.INSTANCE;
		case FP64_LE:
			return FP64Lte.INSTANCE;
		case FP64_EQ:
			return FP64Eq.INSTANCE;
		case BEQ:
			return Beq.INSTANCE;
		case BNEQ:
			return Bneq.INSTANCE;
		case BNOT:
			return bnot;
		case TO_STRING:
			return ToString.INSTANCE;
		case STRING_CMP:
			return StringCmp.INSTANCE;
		case I32_SCMP:
			return I32Scmp.INSTANCE;
		case I32_UCMP:
			return I32Ucmp.INSTANCE;
		case I64_SCMP:
			return I64Scmp.INSTANCE;
		case I64_UCMP:
			return I64Ucmp.INSTANCE;
		case STRING_CONCAT:
			return StringConcat.INSTANCE;
		case STRING_MATCHES:
			return stringMatches;
		case STRING_STARTS_WITH:
			return stringStartsWith;
		case IS_SAT:
			return isSat;
		case IS_SAT_OPT:
			return isSatOpt;
		case IS_SATS:
			return isSats;
		case IS_VALID_OPT:
			return isValidOpt;
		case IS_VALID:
			return isValid;
		case GET_MODEL:
			return getModel;
		case QUERY_MODEL:
			return QueryModel.INSTANCE;
		case SUBSTITUTE:
			return Substitute.INSTANCE;
		case IS_FREE:
			return IsFree.INSTANCE;
		case fp32ToFp64:
			return PrimitiveConversions.fp32ToFp64;
		case fp32ToI32:
			return PrimitiveConversions.fp32ToI32;
		case fp32ToI64:
			return PrimitiveConversions.fp32ToI64;
		case fp64ToFp32:
			return PrimitiveConversions.fp64ToFp32;
		case fp64ToI32:
			return PrimitiveConversions.fp64ToI32;
		case fp64ToI64:
			return PrimitiveConversions.fp64ToI64;
		case i32ToFp32:
			return PrimitiveConversions.i32ToFp32;
		case i32ToFp64:
			return PrimitiveConversions.i32ToFp64;
		case i32ToI64:
			return PrimitiveConversions.i32ToI64;
		case i64ToFp32:
			return PrimitiveConversions.i64ToFp32;
		case i64ToFp64:
			return PrimitiveConversions.i64ToFp64;
		case i64ToI32:
			return PrimitiveConversions.i64ToI32;
		case PRINT:
			return Print.INSTANCE;
		}
		throw new AssertionError();
	}

	private enum I32Add implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_ADD;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return I32.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum I32Sub implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_SUB;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return I32.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum I32Mul implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_MUL;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return I32.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum I32Div implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_DIV;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return I32.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum I32Rem implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_REM;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return I32.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum I32Gt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_GT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum I32Gte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_GE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum I32Lt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_LT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum I32Lte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_LE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum I32And implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_AND;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return I32.make(arg1.getVal() & arg2.getVal());
		}

	}

	private enum I32Or implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_OR;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return I32.make(arg1.getVal() | arg2.getVal());
		}

	}

	private enum I32Xor implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_XOR;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			I32 arg2 = (I32) args[1];
			return I32.make(arg1.getVal() ^ arg2.getVal());
		}

	}

	private enum I32Neg implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_NEG;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I32 arg1 = (I32) args[0];
			return I32.make(-arg1.getVal());
		}

	}

	private enum I64Add implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_ADD;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return I64.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum I64Sub implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_SUB;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return I64.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum I64Mul implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_MUL;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return I64.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum I64Div implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_DIV;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return I64.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum I64Rem implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_REM;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return I64.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum I64Gt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_GT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum I64Gte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_GE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum I64Lt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_LT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum I64Lte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_LE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum I64And implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_AND;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return I64.make(arg1.getVal() & arg2.getVal());
		}

	}

	private enum I64Or implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_OR;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return I64.make(arg1.getVal() | arg2.getVal());
		}

	}

	private enum I64Xor implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_XOR;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			I64 arg2 = (I64) args[1];
			return I64.make(arg1.getVal() ^ arg2.getVal());
		}

	}

	private enum I64Neg implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_NEG;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			I64 arg1 = (I64) args[0];
			return I64.make(-arg1.getVal());
		}

	}

	private enum FP32Add implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_ADD;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return FP32.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum FP32Sub implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_SUB;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return FP32.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum FP32Mul implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_MUL;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return FP32.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum FP32Div implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_DIV;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return FP32.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum FP32Rem implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_REM;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return FP32.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum FP32Gt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_GT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum FP32Gte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_GE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum FP32Lt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_LT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum FP32Lte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_LE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum FP32Eq implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_EQ;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			FP32 arg2 = (FP32) args[1];
			return boolToBoolTerm(arg1.getVal().floatValue() == arg2.getVal().floatValue());
		}

	}

	private enum FP32Neg implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_NEG;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP32 arg1 = (FP32) args[0];
			return FP32.make(-arg1.getVal());
		}

	}

	private enum FP64Add implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_ADD;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return FP64.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum FP64Sub implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_SUB;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return FP64.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum FP64Mul implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_MUL;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return FP64.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum FP64Div implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_DIV;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return FP64.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum FP64Rem implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_REM;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return FP64.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum FP64Gt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_GT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum FP64Gte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_GE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum FP64Lt implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_LT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum FP64Lte implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_LE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum FP64Eq implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_EQ;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			FP64 arg2 = (FP64) args[1];
			return boolToBoolTerm(arg1.getVal().doubleValue() == arg2.getVal().doubleValue());
		}

	}

	private enum FP64Neg implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_NEG;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			FP64 arg1 = (FP64) args[0];
			return FP64.make(-arg1.getVal());
		}

	}

	private enum Beq implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.BEQ;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			Term arg1 = args[0];
			Term arg2 = args[1];
			return boolToBoolTerm(arg1.equals(arg2));
		}

	}

	private enum Bneq implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.BNEQ;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			Term arg1 = args[0];
			Term arg2 = args[1];
			return boolToBoolTerm(!arg1.equals(arg2));
		}

	}

	private static final FunctionDef bnot = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.BNOT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			Term arg = args[0];
			if (arg.equals(trueTerm)) {
				return falseTerm;
			}
			return trueTerm;
		}

	};

	private enum ToString implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.TO_STRING;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			Term arg = args[0];
			if (arg instanceof StringTerm) {
				return arg;
			}
			return StringTerm.make(args[0].toString());
		}

	}

	private enum StringCmp implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.STRING_CMP;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			String s1 = ((StringTerm) args[0]).getVal();
			String s2 = ((StringTerm) args[1]).getVal();
			return makeCmp(s1, s2, (x, y) -> x.compareTo(y));
		}

	}

	private enum I32Scmp implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_SCMP;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			int x = ((I32) args[0]).getVal();
			int y = ((I32) args[1]).getVal();
			return makeCmp(x, y, Integer::compare);
		}

	}

	private enum I32Ucmp implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I32_UCMP;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			int x = ((I32) args[0]).getVal();
			int y = ((I32) args[1]).getVal();
			return makeCmp(x, y, Integer::compareUnsigned);
		}

	}

	private enum I64Scmp implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_SCMP;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			long x = ((I64) args[0]).getVal();
			long y = ((I64) args[1]).getVal();
			return makeCmp(x, y, Long::compare);
		}

	}

	private enum I64Ucmp implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.I64_UCMP;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			long x = ((I64) args[0]).getVal();
			long y = ((I64) args[1]).getVal();
			return makeCmp(x, y, Long::compareUnsigned);
		}

	}

	private enum StringConcat implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.STRING_CONCAT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			String s1 = ((StringTerm) args[0]).getVal();
			String s2 = ((StringTerm) args[1]).getVal();
			return StringTerm.make(s1 + s2);
		}

	}

	private static final FunctionDef stringMatches = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.STRING_MATCHES;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			String str = ((StringTerm) args[0]).getVal();
			String re = ((StringTerm) args[1]).getVal();
			return boolToBoolTerm(str.matches(re));
		}

	};

	private static final FunctionDef stringStartsWith = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.STRING_STARTS_WITH;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			String str = ((StringTerm) args[0]).getVal();
			String pre = ((StringTerm) args[1]).getVal();
			return boolToBoolTerm(str.startsWith(pre));
		}

	};

	private enum Substitute implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.SUBSTITUTE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SolverVariable x = (SolverVariable) args[0];
			SmtLibTerm y = (SmtLibTerm) args[1];
			SmtLibTerm t = (SmtLibTerm) args[2];
			return t.substSolverTerms(HashTreePMap.singleton(x, y));
		}

	}

	private enum IsFree implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.IS_FREE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			Set<SolverVariable> vars = ((SmtLibTerm) args[1]).freeVars();
			SolverVariable x = (SolverVariable) args[0];
			if (vars.contains(x)) {
				return trueTerm;
			} else {
				return falseTerm;
			}
		}

	}

	private final Map<Triple<Object, Boolean, Integer>, Future<Pair<Status, Model>>> smtMemo = new ConcurrentHashMap<>();

	private Pair<Status, Model> querySmt(Object assertions, boolean getModel) throws EvaluationException {
		return querySmt(assertions, getModel, Integer.MAX_VALUE);
	}

	@SuppressWarnings("unchecked")
	private Pair<Status, Model> querySmt(Object assertions, boolean getModel, int timeout)
			throws EvaluationException {
		if (timeout < 0) {
			timeout = -1;
		}
		Triple<Object, Boolean, Integer> key = new Triple<>(assertions, getModel, timeout);
		Future<Pair<Status, Model>> fut = smtMemo.get(key);
		if (fut == null) {
			CompletableFuture<Pair<Status, Model>> completableFut = new CompletableFuture<>();
			fut = completableFut;
			Future<Pair<Status, Model>> fut2 = smtMemo.putIfAbsent(key, fut);
			if (fut2 != null) {
				fut = fut2;
			} else {
				Pair<Status, Map<SolverVariable, Term>> p;
				if (assertions instanceof SmtLibTerm) {
					p = smt.check((SmtLibTerm) assertions, getModel, timeout);
				} else {
					assert assertions instanceof List<?>;
					p = smt.check((List<SmtLibTerm>) assertions, getModel, timeout);
				}
				Map<SolverVariable, Term> m = p.snd();
				Model model = m == null ? null : Model.make(m);
				completableFut.complete(new Pair<>(p.fst(), model));
			}
		}
		try {
			long start = 0;
			if (Configuration.timeSmt) {
				start = System.currentTimeMillis();
			}
			Pair<Status, Model> p = fut.get();
			if (Configuration.timeSmt) {
				long end = System.currentTimeMillis();
				Configuration.recordSmtWaitTime(end - start);
			}
			return p;
		} catch (InterruptedException | ExecutionException e) {
			throw new EvaluationException(e);
		}	
	}
	
	private final FunctionDef isSat = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.IS_SAT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0];
			Pair<Status, Model> p = querySmt(formula, false);
			switch (p.fst()) {
			case SATISFIABLE:
				return trueTerm;
			case UNKNOWN:
				throw new EvaluationException("Z3 returned \"unknown\"");
			case UNSATISFIABLE:
				return falseTerm;
			}
			throw new AssertionError("impossible");
		}

	};

	private final FunctionDef isSatOpt = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.IS_SAT_OPT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0];
			Constructor timeoutOpt = (Constructor) args[1];
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Pair<Status, Model> p = querySmt(formula, false, timeout);
			switch (p.fst()) {
			case SATISFIABLE:
				return some(trueTerm);
			case UNKNOWN:
				return none;
			case UNSATISFIABLE:
				return some(falseTerm);
			}
			throw new AssertionError("impossible");
		}

	};
	
	private final FunctionDef isSats = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.IS_SATS;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0];
			List<SmtLibTerm> assertions = Terms.termToTermList(formula);
			Constructor timeoutOpt = (Constructor) args[1];
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Pair<Status, Model> p = querySmt(assertions, false, timeout);
			switch (p.fst()) {
			case SATISFIABLE:
				return some(trueTerm);
			case UNKNOWN:
				return none;
			case UNSATISFIABLE:
				return some(falseTerm);
			}
			throw new AssertionError("impossible");
		}

	};

	private final FunctionDef isValidOpt = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.IS_VALID_OPT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0];
			formula = (SmtLibTerm) Constructors.make(BuiltInConstructorSymbol.SMT_NOT, Terms.singletonArray(formula));
			Constructor timeoutOpt = (Constructor) args[1];
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Pair<Status, Model> p = querySmt(formula, false, timeout);
			switch (p.fst()) {
			case SATISFIABLE:
				return some(falseTerm);
			case UNKNOWN:
				return none;
			case UNSATISFIABLE:
				return some(trueTerm);
			}
			throw new AssertionError("impossible");
		}

	};

	private final FunctionDef isValid = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.IS_VALID;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0];
			formula = (SmtLibTerm) Constructors.make(BuiltInConstructorSymbol.SMT_NOT, args);
			Pair<Status, Model> p = querySmt(formula, false);
			switch (p.fst()) {
			case SATISFIABLE:
				return falseTerm;
			case UNKNOWN:
				throw new EvaluationException("Z3 returned \"unknown\"");
			case UNSATISFIABLE:
				return trueTerm;
			}
			throw new AssertionError("impossible");
		}

	};

	private static int extractOptionalTimeout(Constructor opt) {
		if (opt.getSymbol().equals(BuiltInConstructorSymbol.SOME)) {
			return ((I32) opt.getArgs()[0]).getVal();
		}
		return Integer.MAX_VALUE;
	}

	private final FunctionDef getModel = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.GET_MODEL;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0];
			Constructor timeoutOpt = (Constructor) args[1];
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Pair<Status, Model> p = querySmt(formula, true, timeout);
			Model model = p.snd();
			return model == null ? none : some(model);
		}

	};

	private enum QueryModel implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.QUERY_MODEL;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			SolverVariable x = (SolverVariable) args[0];
			Model m = (Model) args[1];
			Term t = m.getVal().get(x);
			return t == null ? none : some(t);
		}

	}

	private static final Term none = Constructors.makeZeroAry(BuiltInConstructorSymbol.NONE);

	private static Term some(Term arg) {
		return Constructors.make(BuiltInConstructorSymbol.SOME, Terms.singletonArray(arg));
	}

	private static final Term trueTerm = BoolTerm.mkTrue();
	private static final Term falseTerm = BoolTerm.mkFalse();

	private static Term boolToBoolTerm(boolean b) {
		if (b) {
			return trueTerm;
		} else {
			return falseTerm;
		}
	}

	private enum Print implements FunctionDef {

		INSTANCE;

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.PRINT;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			System.out.println(args[0]);
			return trueTerm;
		}

	}

	private static <T> Term makeCmp(T x, T y, BiFunction<T, T, Integer> cmp) {
		int z = cmp.apply(x, y);
		if (z < 0) {
			return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_LT);
		} else if (z > 0) {
			return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_GT);
		}
		return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_EQ);
	}

}
