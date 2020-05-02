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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Set;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;

public class SmtHpp {

	private final CodeGenContext ctx;

	public SmtHpp(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public void gen(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("smt.hpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("smt.hpp").toFile())) {
			Worker pr = new Worker(out);
			CodeGenUtil.copyOver(br, out, 0);
			pr.copyDeclarations();
			CodeGenUtil.copyOver(br, out, 1);
			pr.genSolverVarCases();
			CodeGenUtil.copyOver(br, out, 2);
			pr.genSerializationCases();
			CodeGenUtil.copyOver(br, out, 3);
			pr.genNeedsTypeAnnotationCases();
			CodeGenUtil.copyOver(br, out, 4);
			pr.genSymbolSerializationCases();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}
	}

	private class Worker {

		private final PrintWriter out;
		private final Set<ConstructorSymbol> varSymbols = new HashSet<>();

		public Worker(PrintWriter out) {
			this.out = out;
			for (ConstructorSymbol sym : ctx.getConstructorSymbols()) {
				if (isVarSymbol(sym)) {
					varSymbols.add(sym);
				}
			}
		}

		private boolean isVarSymbol(ConstructorSymbol sym) {
			return sym instanceof ParameterizedConstructorSymbol
					&& ((ParameterizedConstructorSymbol) sym).getBase() == BuiltInConstructorSymbolBase.SMT_VAR;
		}

		public void copyDeclarations() {
			SmtLibShim shim = new SmtLibShim(null, out);
			shim.initialize(ctx.getEval().getInputProgram(), true);
			try {
				shim.setLogic(Configuration.smtLogic);
				shim.makeDeclarations();
			} catch (EvaluationException e) {
				throw new AssertionError("impossible");
			}
		}

		public void genSolverVarCases() {
			if (varSymbols.isEmpty()) {
				return;
			}
			for (ConstructorSymbol sym : varSymbols) {
				out.println("    case " + ctx.lookupRepr(sym) + ":");
			}
			CppReturn.mk(CppConst.mkTrue()).println(out, 3);
		}

		public void genSerializationCases() {
			for (ConstructorSymbol sym : ctx.getConstructorSymbols()) {
				genSerializationCase(sym);
			}
		}

		private void genSerializationCase(ConstructorSymbol sym) {
			CppStmt stmt = genSerializationCaseBody(sym);
			if (stmt == null) {
				return;
			}
			out.println("    case " + ctx.lookupRepr(sym) + ": {");
			stmt.println(out, 3);
			out.println("      break;");
			out.println("    }");
		}

		private CppStmt genSerializationCaseBody(ConstructorSymbol sym) {
			if (sym instanceof BuiltInConstructorSymbol) {
				return genBuiltInConstructorSymbolCase((BuiltInConstructorSymbol) sym);
			}
			if (sym instanceof ParameterizedConstructorSymbol) {
				return genParameterizedConstructorSymbolCase((ParameterizedConstructorSymbol) sym);
			}
			return null;
		}

		private CppStmt genBuiltInConstructorSymbolCase(BuiltInConstructorSymbol sym) {
			switch (sym) {
			case ARRAY_CONST:
				return genSerializeOp("const");
			case ARRAY_STORE:
				return genSerializeOp("store");
			case BV_ADD:
				return genSerializeOp("bvadd");
			case BV_AND:
				return genSerializeOp("bvand");
			case BV_MUL:
				return genSerializeOp("bvmul");
			case BV_NEG:
				return genSerializeOp("bvneg");
			case BV_OR:
				return genSerializeOp("bvor");
			case BV_SDIV:
				return genSerializeOp("bvsdiv");
			case BV_SREM:
				return genSerializeOp("bvsrem");
			case BV_SUB:
				return genSerializeOp("bvsub");
			case BV_UDIV:
				return genSerializeOp("bvudiv");
			case BV_UREM:
				return genSerializeOp("bvurem");
			case BV_XOR:
				return genSerializeOp("bvxor");
			// Normal constructors don't need special treatment
			case CMP_EQ:
			case CMP_GT:
			case CMP_LT:
			case CONS:
			case NIL:
			case NONE:
			case SOME:
				break;
			case ENTER_FORMULA:
			case EXIT_FORMULA:
				return CppFuncCall.mk("abort").toStmt();
			case FP_ADD:
				return genSerializeOp("fp.add");
			case FP_DIV:
				return genSerializeOp("fp.div");
			case FP_MUL:
				return genSerializeOp("fp.mul");
			case FP_NEG:
				return genSerializeOp("fp.neg");
			case FP_REM:
				return genSerializeOp("fp.rem");
			case FP_SUB:
				return genSerializeOp("fp.sub");
			case INT_ABS:
				return genSerializeOp("abs");
			case INT_ADD:
				return genSerializeOp("+");
			case INT_BIG_CONST:
				return genSerializeInt(true);
			case INT_CONST:
				return genSerializeInt(false);
			case INT_DIV:
				return genSerializeOp("div");
			case INT_GE:
				return genSerializeOp(">=");
			case INT_GT:
				return genSerializeOp(">");
			case INT_LE:
				return genSerializeOp("<=");
			case INT_LT:
				return genSerializeOp("<");
			case INT_MOD:
				return genSerializeOp("mod");
			case INT_MUL:
				return genSerializeOp("*");
			case INT_NEG:
			case INT_SUB:
				return genSerializeOp("-");
			case SMT_AND:
				return genSerializeOp("and");
			case SMT_EXISTS:
				return genSerializeQuantifier(true);
			case SMT_FORALL:
				return genSerializeQuantifier(false);
			case SMT_IMP:
				return genSerializeOp("=>");
			case SMT_ITE:
				return genSerializeOp("ite");
			case SMT_NOT:
				return genSerializeOp("not");
			case SMT_OR:
				return genSerializeOp("or");
			case STR_AT:
				return genSerializeOp("str.at");
			case STR_CONCAT:
				return genSerializeOp("str.++");
			case STR_CONTAINS:
				return genSerializeOp("str.contains");
			case STR_INDEXOF:
				return genSerializeOp("str.indexof");
			case STR_LEN:
				return genSerializeOp("str.len");
			case STR_PREFIXOF:
				return genSerializeOp("str.prefixof");
			case STR_REPLACE:
				return genSerializeOp("str.replace");
			case STR_SUBSTR:
				return genSerializeOp("str.substr");
			case STR_SUFFIXOF:
				return genSerializeOp("str.suffixof");
			}
			return null;
		}

		private int index(ParameterizedConstructorSymbol sym, int i) {
			return ((TypeIndex) sym.getArgs().get(i).getType()).getIndex();
		}

		private CppStmt mkCall(String func) {
			return CppFuncCall.mk(func, CppVar.mk("t")).toStmt();
		}

		private CppStmt genParameterizedConstructorSymbolCase(ParameterizedConstructorSymbol sym) {
			switch (sym.getBase()) {
			case ARRAY_DEFAULT:
				return genSerializeOp("default");
			case ARRAY_SELECT:
				return genSerializeOp("select");
			case BV_BIG_CONST:
				return genSerializeBitString(index(sym, 0), true);
			case BV_CONST:
				return genSerializeBitString(index(sym, 0), false);
			case BV_SGE:
				return genSerializeOp("bvsge");
			case BV_SGT:
				return genSerializeOp("bvsgt");
			case BV_SLE:
				return genSerializeOp("bvsle");
			case BV_SLT:
				return genSerializeOp("bvslt");
			case BV_TO_BV_SIGNED:
				return genSerializeBvToBv(index(sym, 0), index(sym, 1), true);
			case BV_TO_BV_UNSIGNED:
				return genSerializeBvToBv(index(sym, 0), index(sym, 1), false);
			case BV_TO_FP: {
				int exp = index(sym, 1);
				int sig = index(sym, 2);
				String func = "serialize_bv_to_fp<" + exp + ", " + sig + ">";
				return mkCall(func);
			}
			case BV_UGE:
				return genSerializeOp("bvuge");
			case BV_UGT:
				return genSerializeOp("bvugt");
			case BV_ULE:
				return genSerializeOp("bvule");
			case BV_ULT:
				return genSerializeOp("bvult");
			case FP_BIG_CONST: {
				int exp = index(sym, 0);
				int sig = index(sym, 1);
				return genSerializeFp(exp, sig, true);
			}
			case FP_CONST: {
				int exp = index(sym, 0);
				int sig = index(sym, 1);
				return genSerializeFp(exp, sig, false);
			}
			case FP_EQ:
				return genSerializeOp("fp.eq");
			case FP_GE:
				return genSerializeOp("fp.geq");
			case FP_GT:
				return genSerializeOp("fp.gt");
			case FP_IS_NAN:
				return genSerializeOp("fp.isNaN");
			case FP_LE:
				return genSerializeOp("fp.leq");
			case FP_LT:
				return genSerializeOp("fp.lt");
			case FP_TO_SBV:
				return genSerializeFpToBv(index(sym, 2), true);
			case FP_TO_UBV:
				return genSerializeFpToBv(index(sym, 2), false);
			case FP_TO_FP: {
				int exp = index(sym, 2);
				int sig = index(sym, 3);
				String func = "serialize_fp_to_fp<" + exp + ", " + sig + ">";
				return mkCall(func);
			}
			case SMT_EQ:
				return genSerializeOp("=");
			case SMT_LET:
				return mkCall("serialize_let");
			case SMT_VAR: {
				CppExpr call = CppMethodCall.mk(CppVar.mk("shim"), "lookup_var", CppVar.mk("t"));
				return CppBinop.mkShiftLeft(CppVar.mk("out"), call).toStmt();
			}
			case SMT_PAT:
			case SMT_WRAP_VAR:
				return CppFuncCall.mk("abort").toStmt();
			}
			return null;
		}

		private CppStmt genSerializeOp(String op) {
			CppExpr s = CppConst.mkString(op);
			CppExpr t = CppMethodCall.mkThruPtr(CppVar.mk("t"), "as_complex");
			return CppFuncCall.mk("serialize", s, t).toStmt();
		}

		private CppStmt genSerializeBitString(int n, boolean big) {
			String type = big ? "int64_t" : "int32_t";
			String func = "serialize_bit_string<" + type + ", " + n + ">";
			return mkCall(func);
		}

		private CppStmt genSerializeBvToBv(int from, int to, boolean signed) {
			String func = "serialize_bv_to_bv<" + from + ", " + to + ", " + signed + ">";
			return mkCall(func);
		}

		private CppStmt genSerializeFpToBv(int width, boolean signed) {
			String func = "serialize_fp_to_bv<" + width + ", " + signed + ">";
			return mkCall(func);
		}

		private CppStmt genSerializeFp(int e, int s, boolean big) {
			String type = big ? "double" : "float";
			String func = "serialize_fp<" + type + ", " + e + ", " + s + ">";
			CppExpr arg = CppFuncCall.mk("arg0", CppVar.mk("t"));
			return CppFuncCall.mk(func, arg).toStmt();
		}

		private CppStmt genSerializeInt(boolean big) {
			String type = big ? "int64_t" : "int32_t";
			String func = "serialize_int<" + type + ">";
			return mkCall(func);
		}

		private CppStmt genSerializeQuantifier(boolean exists) {
			String func = "serialize_quantifier<" + exists + ">";
			return mkCall(func);
		}

		public void genNeedsTypeAnnotationCases() {
			boolean foundOne = false;
			for (ConstructorSymbol sym : ctx.getConstructorSymbols()) {
				if (SmtLibShim.needsTypeAnnotation(sym)) {
					out.println("    case " + ctx.lookupRepr(sym) + ":");
					foundOne = true;
				}
			}
			if (foundOne) {
				CppReturn.mk(CppConst.mkTrue()).println(out, 3);
			}
		}

		public void genSymbolSerializationCases() {
			boolean foundOne = false;
			for (ConstructorSymbol sym : ctx.getConstructorSymbols()) {
				if (sym.getConstructorSymbolType().equals(ConstructorSymbolType.SOLVER_CONSTRUCTOR_TESTER)) {
					out.println("    case " + ctx.lookupRepr(sym) + ":");
					foundOne = true;
				}
			}
			if (foundOne) {
				CppExpr call = CppFuncCall.mk("serialize_tester", CppVar.mk("sym"));
				CppReturn.mk(call).println(out, 3);
			}
		}

	}

}
