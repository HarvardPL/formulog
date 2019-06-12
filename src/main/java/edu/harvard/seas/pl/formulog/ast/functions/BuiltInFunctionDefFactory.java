package edu.harvard.seas.pl.formulog.ast.functions;

import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;

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
import edu.harvard.seas.pl.formulog.smt.Z3Process;
import edu.harvard.seas.pl.formulog.smt.Z3Thread;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

// TODO Break this up into different classes; pass them into BuiltInFunctionSymbol
public final class BuiltInFunctionDefFactory {

	private final Z3Process z3;
	
	public BuiltInFunctionDefFactory(SymbolManager symbolManager) {
		z3 = new Z3Process(symbolManager);
		z3.start();
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
		case ANDB:
			return Andb.INSTANCE;
		case ORB:
			return Orb.INSTANCE;
		case NEGB:
			return Negb.INSTANCE;
		case ITE:
			return Ite.INSTANCE;
		case STRING_OF_I32:
			return StringOfI32.INSTANCE;
		case STRCMP:
			return Strcmp.INSTANCE;
		case I32CMP:
			return I32cmp.INSTANCE;
		case STRCAT:
			return Strcat.INSTANCE;
		case IS_SAT:
			return isSat;
		case IS_SAT_OPT:
			return isSatOpt;
		case IS_VALID_OPT:
			return isValidOpt;
		case IS_VALID:
			return isValid;
		case GET_MODEL:
			return getModel;
		case QUERY_MODEL:
			return QueryModel.INSTANCE;
		// case PATH_INTERPOLANT:
		// return PathInterpolant.INSTANCE;
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
		case ENTER_FORMULA:
		case EXIT_FORMULA:
			return new Id(sym);
		case PRINT:
			return Print.INSTANCE;
		}
		throw new AssertionError();
	}

	private enum I32Add implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_ADD;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return I32.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum I32Sub implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_SUB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return I32.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum I32Mul implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_MUL;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return I32.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum I32Div implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_DIV;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return I32.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum I32Rem implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_REM;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return I32.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum I32Gt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_GT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum I32Gte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_GE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum I32Lt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_LT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum I32Lte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_LE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum I32And implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_AND;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return I32.make(arg1.getVal() & arg2.getVal());
		}

	}

	private enum I32Or implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_OR;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return I32.make(arg1.getVal() | arg2.getVal());
		}

	}

	private enum I32Xor implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_XOR;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			I32 arg2 = (I32) Terms.lookup(args[1], subst);
			return I32.make(arg1.getVal() ^ arg2.getVal());
		}

	}

	private enum I32Neg implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32_NEG;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 arg1 = (I32) Terms.lookup(args[0], subst);
			return I32.make(-arg1.getVal());
		}

	}

	private enum I64Add implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_ADD;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return I64.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum I64Sub implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_SUB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return I64.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum I64Mul implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_MUL;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return I64.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum I64Div implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_DIV;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return I64.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum I64Rem implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_REM;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return I64.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum I64Gt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_GT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum I64Gte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_GE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum I64Lt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_LT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum I64Lte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_LE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum I64And implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_AND;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return I64.make(arg1.getVal() & arg2.getVal());
		}

	}

	private enum I64Or implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_OR;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return I64.make(arg1.getVal() | arg2.getVal());
		}

	}

	private enum I64Xor implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_XOR;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			I64 arg2 = (I64) Terms.lookup(args[1], subst);
			return I64.make(arg1.getVal() ^ arg2.getVal());
		}

	}

	private enum I64Neg implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I64_NEG;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 arg1 = (I64) Terms.lookup(args[0], subst);
			return I64.make(-arg1.getVal());
		}

	}

	private enum FP32Add implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_ADD;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return FP32.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum FP32Sub implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_SUB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return FP32.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum FP32Mul implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_MUL;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return FP32.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum FP32Div implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_DIV;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return FP32.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum FP32Rem implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_REM;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return FP32.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum FP32Gt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_GT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum FP32Gte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_GE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum FP32Lt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_LT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum FP32Lte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_LE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum FP32Eq implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_EQ;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			FP32 arg2 = (FP32) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal().floatValue() == arg2.getVal().floatValue());
		}

	}

	private enum FP32Neg implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP32_NEG;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 arg1 = (FP32) Terms.lookup(args[0], subst);
			return FP32.make(-arg1.getVal());
		}

	}

	private enum FP64Add implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_ADD;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return FP64.make(arg1.getVal() + arg2.getVal());
		}

	}

	private enum FP64Sub implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_SUB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return FP64.make(arg1.getVal() - arg2.getVal());
		}

	}

	private enum FP64Mul implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_MUL;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return FP64.make(arg1.getVal() * arg2.getVal());
		}

	}

	private enum FP64Div implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_DIV;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Division by zero");
			}
			return FP64.make(arg1.getVal() / arg2.getVal());
		}

	}

	private enum FP64Rem implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_REM;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			if (arg2.getVal() == 0) {
				throw new EvaluationException("Remainder by zero");
			}
			return FP64.make(arg1.getVal() % arg2.getVal());
		}

	}

	private enum FP64Gt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_GT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() > arg2.getVal());
		}

	}

	private enum FP64Gte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_GE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() >= arg2.getVal());
		}

	}

	private enum FP64Lt implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_LT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() < arg2.getVal());
		}

	}

	private enum FP64Lte implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_LE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal() <= arg2.getVal());
		}

	}

	private enum FP64Eq implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_EQ;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			FP64 arg2 = (FP64) Terms.lookup(args[1], subst);
			return boolToBoolTerm(arg1.getVal().doubleValue() == arg2.getVal().doubleValue());
		}

	}

	private enum FP64Neg implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.FP64_NEG;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 arg1 = (FP64) Terms.lookup(args[0], subst);
			return FP64.make(-arg1.getVal());
		}

	}

	private enum Beq implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.BEQ;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Term arg1 = args[0].applySubstitution(subst);
			Term arg2 = args[1].applySubstitution(subst);
			return boolToBoolTerm(arg1.equals(arg2));
		}

	}

	private enum Bneq implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.BNEQ;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Term arg1 = args[0].applySubstitution(subst);
			Term arg2 = args[1].applySubstitution(subst);
			return boolToBoolTerm(!arg1.equals(arg2));
		}

	}

	private enum Andb implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.ANDB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Constructor arg1 = (Constructor) args[0].applySubstitution(subst);
			Constructor arg2 = (Constructor) args[1].applySubstitution(subst);
			return boolToBoolTerm(boolTermToBool(arg1) && boolTermToBool(arg2));
		}

	}

	private enum Orb implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.ORB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Constructor arg1 = (Constructor) args[0].applySubstitution(subst);
			Constructor arg2 = (Constructor) args[1].applySubstitution(subst);
			return boolToBoolTerm(boolTermToBool(arg1) || boolTermToBool(arg2));
		}

	}

	private enum Negb implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.NEGB;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Constructor t = (Constructor) Terms.lookup(args[0], subst);
			return boolToBoolTerm(!boolTermToBool(t));
		}
	}

	private enum Ite implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.ITE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Constructor t = (Constructor) Terms.lookup(args[0], subst);
			if (boolTermToBool(t)) {
				return Terms.lookup(args[1], subst);
			} else {
				return Terms.lookup(args[2], subst);
			}
		}
	}

	private enum StringOfI32 implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.STRING_OF_I32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 x = (I32) Terms.lookup(args[0], subst);
			return StringTerm.make(Integer.toString(x.getVal()));
		}

	}

	private enum Strcmp implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.STRCMP;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			String s1 = ((StringTerm) Terms.lookup(args[0], subst)).getVal();
			String s2 = ((StringTerm) Terms.lookup(args[1], subst)).getVal();
			int cmp = s1.compareTo(s2);
			if (cmp < 0) {
				return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_LT);
			} else if (cmp > 0) {
				return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_GT);
			}
			return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_EQ);
		}

	}

	private enum I32cmp implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.I32CMP;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			int x = ((I32) Terms.lookup(args[0], subst)).getVal();
			int y = ((I32) Terms.lookup(args[1], subst)).getVal();
			int cmp = Integer.compare(x, y);
			if (cmp < 0) {
				return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_LT);
			} else if (cmp > 0) {
				return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_GT);
			}
			return Constructors.makeZeroAry(BuiltInConstructorSymbol.CMP_EQ);
		}

	}

	private enum Strcat implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.STRCAT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			String s1 = ((StringTerm) Terms.lookup(args[0], subst)).getVal();
			String s2 = ((StringTerm) Terms.lookup(args[1], subst)).getVal();
			return StringTerm.make(s1 + s2);
		}

	}

	private enum Substitute implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.SUBSTITUTE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SolverVariable x = (SolverVariable) Terms.lookup(args[0], subst);
			SmtLibTerm y = (SmtLibTerm) Terms.lookup(args[1], subst);
			SmtLibTerm t = (SmtLibTerm) Terms.lookup(args[2], subst);
			return t.substSolverTerms(HashTreePMap.singleton(x, y));
		}

	}

	private enum IsFree implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.IS_FREE;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			Set<SolverVariable> vars = ((SmtLibTerm) Terms.lookup(args[1], subst)).freeVars();
			SolverVariable x = (SolverVariable) Terms.lookup(args[0], subst);
			if (vars.contains(x)) {
				return trueBool;
			} else {
				return falseBool;
			}
		}

	}

	private final Map<Term, Map<Integer, Future<Optional<Model>>>> smtMemo = new ConcurrentHashMap<>();

	private Optional<Model> querySmt(SmtLibTerm formula, int timeout) throws EvaluationException {
		Map<Integer, Future<Optional<Model>>> byTimeout = Util.lookupOrCreate(smtMemo, formula,
				() -> new ConcurrentHashMap<>());
		Future<Optional<Model>> m = byTimeout.get(timeout);
		if (m == null) {
			CompletableFuture<Optional<Model>> future = new CompletableFuture<>();
			m = future;
			Future<Optional<Model>> m2 = byTimeout.putIfAbsent(timeout, m);
			if (m2 != null) {
				m = m2;
			} else {
				Thread thread = Thread.currentThread();
				Z3Process localZ3 = z3;
				if (thread instanceof Z3Thread) {
					localZ3 = ((Z3Thread) thread).getZ3Process();
				} 
				Pair<Status, Map<SolverVariable, Term>> p = localZ3.check(formula, timeout);
				switch (p.fst()) {
				case SATISFIABLE:
					future.complete(Optional.of(Model.make(p.snd())));
					break;
				case UNKNOWN:
					future.complete(null);
					break;
				case UNSATISFIABLE:
					future.complete(Optional.empty());
					break;
				default:
					throw new AssertionError("impossible");
				}
			}
		}
		try {
			return m.get();
		} catch (InterruptedException | ExecutionException e) {
			throw new EvaluationException(e);
		}
	}

	private final FunctionDef isSat = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.IS_SAT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0].applySubstitution(subst);
			Optional<Model> m = querySmt(formula, -1);
			if (m == null) {
				throw new EvaluationException("Z3 returned \"unknown\"");
			}
			if (m.isPresent()) {
				return trueBool;
			} else {
				return falseBool;
			}
		}

	};

	private final FunctionDef isSatOpt = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.IS_SAT_OPT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0].applySubstitution(subst);
			Constructor timeoutOpt = (Constructor) args[1].applySubstitution(subst);
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Optional<Model> m = querySmt(formula, timeout);
			if (m == null) {
				return none;
			}
			if (m.isPresent()) {
				return some(trueBool);
			} else {
				return some(falseBool);
			}
		}

	};

	private final FunctionDef isValidOpt = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.IS_VALID_OPT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0].applySubstitution(subst);
			formula = Constructors.make(BuiltInConstructorSymbol.FORMULA_NOT, Terms.singletonArray(formula));
			Constructor timeoutOpt = (Constructor) args[1].applySubstitution(subst);
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Optional<Model> m = querySmt(formula, timeout);
			if (m == null) {
				return none;
			}
			if (m.isPresent()) {
				return some(falseBool);
			} else {
				return some(trueBool);
			}
		}

	};

	private final FunctionDef isValid = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.IS_VALID;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0].applySubstitution(subst);
			formula = Constructors.make(BuiltInConstructorSymbol.FORMULA_NOT, args);
			Optional<Model> m = querySmt(formula, -1);
			if (m == null) {
				throw new EvaluationException("Z3 returned \"unknown\"");
			}
			if (m.isPresent()) {
				return falseBool;
			} else {
				return trueBool;
			}
		}

	};

	private static int extractOptionalTimeout(Constructor opt) {
		if (opt.getSymbol().equals(BuiltInConstructorSymbol.SOME)) {
			return ((I32) opt.getArgs()[0]).getVal();
		}
		return -1;
	}

	private final FunctionDef getModel = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.GET_MODEL;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SmtLibTerm formula = (SmtLibTerm) args[0].applySubstitution(subst);
			Constructor timeoutOpt = (Constructor) args[1].applySubstitution(subst);
			Integer timeout = extractOptionalTimeout(timeoutOpt);
			Optional<Model> m = querySmt(formula, timeout);
			return m == null || !m.isPresent() ? none : some(m.get());
		}

	};

	private enum QueryModel implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.QUERY_MODEL;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			SolverVariable x = (SolverVariable) Terms.lookup(args[0], subst);
			Model m = (Model) Terms.lookup(args[1], subst);
			Term t = m.getVal().get(x);
			return t == null ? none : some(t);
		}

	}

	private static final Constructor none = Constructors.makeZeroAry(BuiltInConstructorSymbol.NONE);

	private static Constructor some(Term arg) {
		return Constructors.make(BuiltInConstructorSymbol.SOME, Terms.singletonArray(arg));
	}

	private static final Constructor trueBool = Constructors.makeTrue();
	private static final Constructor falseBool = Constructors.makeFalse();

	private static boolean boolTermToBool(Constructor b) {
		if (b.equals(trueBool)) {
			return true;
		}
		if (b.equals(falseBool)) {
			return false;
		}
		throw new AssertionError();
	}

	private static Constructor boolToBoolTerm(boolean b) {
		if (b) {
			return trueBool;
		} else {
			return falseBool;
		}
	}

	private static class Id implements FunctionDef {

		private final Symbol sym;

		public Id(Symbol sym) {
			assert sym.getArity() == 1;
			this.sym = sym;
		}

		@Override
		public Symbol getSymbol() {
			return sym;
		}

		@Override
		public Term evaluate(Term[] args, Substitution substitution) throws EvaluationException {
			return args[0].applySubstitution(substitution);
		}

	}

	private enum Print implements FunctionDef {

		INSTANCE;

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.PRINT;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			System.out.println(Terms.lookup(args[0], subst));
			return trueBool;
		}

	}

	// private enum PathInterpolant implements FunctionDef {
	//
	// INSTANCE;
	//
	// @Override
	// public Symbol getSymbol() {
	// return BuiltInFunctionSymbol.PATH_INTERPOLANT;
	// }
	//
	// @Override
	// public Term evaluate(Term[] args, Substitution subst) throws
	// EvaluationException {
	// throw new AssertionError();
	//// ConstraintSolver solver = new ConstraintSolver();
	//// Term[] res =
	// solver.getPathInterpolants(listTermToArray(args[0].applySubstitution(subst)));
	//// if (res == null) {
	//// return Constructor.getZeroAry(BuiltInConstructorSymbol.NONE);
	//// }
	//// return Constructor.get(BuiltInConstructorSymbol.SOME, new Term[] {
	// arrayToListTerm(res) });
	// }
	//
	// }

	// private static Term[] listTermToArray(Term list) {
	// return listTermToList(list).toArray(Terms.EMPTY_TERMS_ARR);
	// }
	//
	// private static List<Term> listTermToList(Term t) {
	// List<Term> l = listTermToList(t, new ArrayList<>());
	// return l;
	// }
	//
	// private static List<Term> listTermToList(Term t, List<Term> acc) {
	// assert t instanceof Constructor;
	// Constructor c = (Constructor) t;
	// Symbol sym = c.getSymbol();
	// assert sym instanceof BuiltInConstructorSymbol;
	// switch ((BuiltInConstructorSymbol) sym) {
	// case NIL:
	// return acc;
	// case CONS:
	// Term hd = c.getArgs()[0];
	// Term tl = c.getArgs()[1];
	// acc.add(hd);
	// return listTermToList(tl, acc);
	// default:
	// throw new AssertionError();
	// }
	// }
	//
	// private static Term arrayToListTerm(Term[] terms) {
	// Term t = Constructor.getZeroAry(BuiltInConstructorSymbol.NIL);
	// for (int i = terms.length - 1; i >= 0; --i) {
	// t = Constructor.get(BuiltInConstructorSymbol.CONS, new Term[] { terms[i], t
	// });
	// }
	// return t;
	// }

}
