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

import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
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
			new SmtLibShim(null, out, ctx.getEval().getInputProgram());
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
				break;
			case ARRAY_STORE:
				break;
			case BV_ADD:
				break;
			case BV_AND:
				break;
			case BV_MUL:
				break;
			case BV_NEG:
				break;
			case BV_OR:
				break;
			case BV_SDIV:
				break;
			case BV_SREM:
				break;
			case BV_SUB:
				break;
			case BV_UDIV:
				break;
			case BV_UREM:
				break;
			case BV_XOR:
				break;
			case CMP_EQ:
				break;
			case CMP_GT:
				break;
			case CMP_LT:
				break;
			case CONS:
				break;
			case ENTER_FORMULA:
			case EXIT_FORMULA:
				throw new AssertionError("impossible");
			case FP_ADD:
				break;
			case FP_DIV:
				break;
			case FP_MUL:
				break;
			case FP_NEG:
				break;
			case FP_REM:
				break;
			case FP_SUB:
				break;
			case INT_ABS:
				break;
			case INT_ADD:
				break;
			case INT_BIG_CONST:
				break;
			case INT_CONST:
				break;
			case INT_DIV:
				break;
			case INT_GE:
				break;
			case INT_GT:
				break;
			case INT_LE:
				break;
			case INT_LT:
				break;
			case INT_MOD:
				break;
			case INT_MUL:
				break;
			case INT_NEG:
				break;
			case INT_SUB:
				break;
			case NIL:
				break;
			case NONE:
				break;
			case SMT_AND:
				return genSerializeOp("and");
			case SMT_EXISTS:
				break;
			case SMT_FORALL:
				break;
			case SMT_IMP:
				return genSerializeOp("=>");
			case SMT_ITE:
				return genSerializeOp("ite");
			case SMT_NOT:
				return genSerializeOp("not");
			case SMT_OR:
				return genSerializeOp("or");
			case SOME:
				break;
			case STR_AT:
				break;
			case STR_CONCAT:
				break;
			case STR_CONTAINS:
				break;
			case STR_INDEXOF:
				break;
			case STR_LEN:
				break;
			case STR_PREFIXOF:
				break;
			case STR_REPLACE:
				break;
			case STR_SUBSTR:
				break;
			case STR_SUFFIXOF:
				break;
			}
			return null;
		}

		private int index(ParameterizedConstructorSymbol sym, int i) {
			return ((TypeIndex) sym.getArgs().get(i).getType()).getIndex();
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
				return genSerializeBvConv(index(sym, 0), index(sym, 1), true);
			case BV_TO_BV_UNSIGNED:
				return genSerializeBvConv(index(sym, 0), index(sym, 1), false);
			case BV_TO_FP: {
				int exp = index(sym, 1);
				int sig = index(sym, 2);
				String func = "serialize_bv_to_fp<" + exp + ", " + sig + ">";
				return CppFuncCall.mk(func, CppVar.mk("t")).toStmt();
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
			case FP_TO_BV:
				break;
			case FP_TO_FP:
				break;
			case SMT_EQ:
				return genSerializeOp("=");
			case SMT_LET:
				break;
			case SMT_PAT:
				break;
			case SMT_VAR: {
				CppExpr call = CppMethodCall.mk(CppVar.mk("shim"), "lookup_var", CppVar.mk("t"));
				return CppBinop.mkShiftLeft(CppVar.mk("out"), call).toStmt();
			}
			case SMT_WRAP_VAR:
				break;
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
			return CppFuncCall.mk(func, CppVar.mk("t")).toStmt();
		}
		
		private CppStmt genSerializeBvConv(int from, int to, boolean signed) {
			String func = "serialize_bv_conv<" + from + ", " + to + ", " + signed + ">";
			return CppFuncCall.mk(func, CppVar.mk("t")).toStmt();
		}
		
		private CppStmt genSerializeFp(int e, int s, boolean big) {
			String type = big ? "double" : "float";
			String func = "serialize_fp<" + type + ", " + e + ", " + s + ">";
			CppExpr arg = CppFuncCall.mk("arg0", CppVar.mk("t"));
			return CppFuncCall.mk(func, arg).toStmt();
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

	}

}
