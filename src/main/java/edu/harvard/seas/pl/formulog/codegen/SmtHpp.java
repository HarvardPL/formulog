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
			pr.genVisitingCases();
			CodeGenUtil.copyOver(br, out, 2);
			pr.genSerializationCases();
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

		public void genVisitingCases() {
			if (varSymbols.isEmpty()) {
				return;
			}
			for (ConstructorSymbol sym : varSymbols) {
				out.println("    case " + ctx.lookupRepr(sym) + ":");
			}
			CppFuncCall.mk("SmtShim::record_var", CppVar.mk("t")).toStmt().println(out, 3);
			out.println("      break;");
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
				return genOp("and");
			case SMT_EXISTS:
				break;
			case SMT_FORALL:
				break;
			case SMT_IMP:
				return genOp("=>");
			case SMT_ITE:
				return genOp("ite");
			case SMT_NOT:
				return genOp("not");
			case SMT_OR:
				return genOp("or");
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

		private CppStmt genParameterizedConstructorSymbolCase(ParameterizedConstructorSymbol sym) {
			switch (sym.getBase()) {
			case ARRAY_DEFAULT:
				break;
			case ARRAY_SELECT:
				break;
			case BV_BIG_CONST:
				break;
			case BV_CONST:
				break;
			case BV_SGE:
				break;
			case BV_SGT:
				break;
			case BV_SLE:
				break;
			case BV_SLT:
				break;
			case BV_TO_BV_SIGNED:
				break;
			case BV_TO_BV_UNSIGNED:
				break;
			case BV_TO_FP:
				break;
			case BV_UGE:
				break;
			case BV_UGT:
				break;
			case BV_ULE:
				break;
			case BV_ULT:
				break;
			case FP_BIG_CONST:
				break;
			case FP_CONST:
				break;
			case FP_EQ:
				break;
			case FP_GE:
				break;
			case FP_GT:
				break;
			case FP_IS_NAN:
				break;
			case FP_LE:
				break;
			case FP_LT:
				break;
			case FP_TO_BV:
				break;
			case FP_TO_FP:
				break;
			case SMT_EQ:
				return genOp("=");
			case SMT_LET:
				break;
			case SMT_PAT:
				break;
			case SMT_VAR:
				return CppBinop.mkShiftLeft(CppVar.mk("out"), CppFuncCall.mk("lookup_var", CppVar.mk("t"))).toStmt();
			case SMT_WRAP_VAR:
				break;
			}
			return null;
		}

		private CppStmt genOp(String op) {
			CppExpr s = CppConst.mkString(op);
			CppExpr t = CppMethodCall.mkThruPtr(CppVar.mk("t"), "as_complex");
			CppExpr o = CppVar.mk("out");
			return CppFuncCall.mk("serialize", s, t, o).toStmt();
		}

	}

}
