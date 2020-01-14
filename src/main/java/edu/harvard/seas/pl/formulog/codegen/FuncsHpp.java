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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.TodoException;

public class FuncsHpp {

	private final CodeGenContext ctx;
	
	public FuncsHpp(CodeGenContext ctx) {
		this.ctx = ctx;
	}
	
	public void gen(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("funcs.hpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("funcs.hpp").toFile())) {
			Worker pr = new Worker(out);
			CodeGenUtil.copyOver(br, out, 0);
			pr.makeDeclarations();
			CodeGenUtil.copyOver(br, out, 1);
			pr.makeDefinitions();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}		
	}
	
	private class Worker {
		
		private final PrintWriter out;
		private final Set<FunctionSymbol> userDefinedFunctions = new HashSet<>();
		private final TermCodeGen tcg = new TermCodeGen(ctx);
		
		public Worker(PrintWriter out) {
			this.out = out;
		}
		
		private void makeDeclarations() {
			for (FunctionSymbol sym : ctx.getEval().getInputProgram().getFunctionSymbols()) {
				if (sym instanceof BuiltInFunctionSymbol) {
					registerBuiltInFunction((BuiltInFunctionSymbol) sym);
				} else if (sym instanceof PredicateFunctionSymbol) {
					throw new TodoException();
				} else {
					declareUserDefinedFunction(sym);
				}
			}
		}
		
		private void declareUserDefinedFunction(FunctionSymbol sym) {
			String name = mkName(sym);
			ctx.register(sym, name);
			userDefinedFunctions.add(sym);
			out.println();
			out.print("term_ptr " + name + "(");
			int n = sym.getArity();
			for (int i = 0; i < n; ++i) {
				out.print("const term_ptr&");
				if (i < n - 1) {
					out.print(", ");
				}
			}
			out.println(");");
		}
		
		private String mkName(FunctionSymbol sym) {
			return sym.toString().replaceAll("[^A-Za-z0-9_]", "__");
		}
		
		private void registerBuiltInFunction(BuiltInFunctionSymbol sym) {
			switch (sym) {
			case BEQ:
				ctx.register(sym, "beq");
				break;
			case BNEQ:
				ctx.register(sym, "bneq");
				break;
			case BNOT:
				ctx.register(sym, "bnot");
				break;
			case FP32_ADD:
				break;
			case FP32_DIV:
				break;
			case FP32_EQ:
				break;
			case FP32_GE:
				break;
			case FP32_GT:
				break;
			case FP32_LE:
				break;
			case FP32_LT:
				break;
			case FP32_MUL:
				break;
			case FP32_NEG:
				break;
			case FP32_REM:
				break;
			case FP32_SUB:
				break;
			case FP64_ADD:
				break;
			case FP64_DIV:
				break;
			case FP64_EQ:
				break;
			case FP64_GE:
				break;
			case FP64_GT:
				break;
			case FP64_LE:
				break;
			case FP64_LT:
				break;
			case FP64_MUL:
				break;
			case FP64_NEG:
				break;
			case FP64_REM:
				break;
			case FP64_SUB:
				break;
			case GET_MODEL:
				break;
			case I32_ADD:
				ctx.register(sym, "add<int32_t>");
				break;
			case I32_AND:
				ctx.register(sym, "bitwise_and<int32_t>");
				break;
			case I32_DIV:
				ctx.register(sym, "div<int32_t>");
				break;
			case I32_GE:
				break;
			case I32_GT:
				break;
			case I32_LE:
				break;
			case I32_LT:
				break;
			case I32_MUL:
				ctx.register(sym, "mul<int32_t>");
				break;
			case I32_NEG:
				ctx.register(sym, "neg<int32_t>");
				break;
			case I32_OR:
				ctx.register(sym, "bitwise_or<int32_t>");
				break;
			case I32_REM:
				ctx.register(sym, "rem<int32_t>");
				break;
			case I32_SCMP:
				break;
			case I32_SUB:
				ctx.register(sym, "sub<int32_t>");
				break;
			case I32_UCMP:
				break;
			case I32_XOR:
				ctx.register(sym, "bitwise_xor<int32_t>");
				break;
			case I64_ADD:
				break;
			case I64_AND:
				break;
			case I64_DIV:
				break;
			case I64_GE:
				break;
			case I64_GT:
				break;
			case I64_LE:
				break;
			case I64_LT:
				break;
			case I64_MUL:
				break;
			case I64_NEG:
				break;
			case I64_OR:
				break;
			case I64_REM:
				break;
			case I64_SCMP:
				break;
			case I64_SUB:
				break;
			case I64_UCMP:
				break;
			case I64_XOR:
				break;
			case IS_FREE:
				break;
			case IS_SAT:
				break;
			case IS_SAT_OPT:
				break;
			case IS_VALID:
				break;
			case IS_VALID_OPT:
				break;
			case PRINT:
				break;
			case QUERY_MODEL:
				break;
			case STRCAT:
				break;
			case STRCMP:
				break;
			case STRING_MATCHES:
				break;
			case STRING_OF_I32:
				break;
			case STRING_STARTS_WITH:
				break;
			case SUBSTITUTE:
				break;
			case fp32ToFp64:
				break;
			case fp32ToI32:
				break;
			case fp32ToI64:
				break;
			case fp64ToFp32:
				break;
			case fp64ToI32:
				break;
			case fp64ToI64:
				break;
			case i32ToFp32:
				break;
			case i32ToFp64:
				break;
			case i32ToI64:
				break;
			case i64ToFp32:
				break;
			case i64ToFp64:
				break;
			case i64ToI32:
				break;
			}
		}
		
		private void makeDefinitions() {
			for (FunctionSymbol sym : userDefinedFunctions) {
				makeDefinitionForUserDefinedFunc(sym);
			}
		}
		
		private void makeDefinitionForUserDefinedFunc(FunctionSymbol sym) {
			UserFunctionDef def = (UserFunctionDef) ctx.getEval().getInputProgram().getDef(sym);
			out.println();
			out.print("term_ptr " + ctx.lookupRepr(sym) + "(");
			Map<Var, CppExpr> env = new HashMap<>();
			Iterator<Var> params = def.getParams().iterator();
			int n = sym.getArity();
			for (int i = 0; i < n; ++i) {
				String id = ctx.newId("x");
				CppVar var = CppVar.mk(id);
				env.put(params.next(), var);
				out.print("const term_ptr& ");
				var.print(out);
				if (i < n - 1) {
					out.print(", ");
				}
			}
			out.println(") {");
			Pair<CppStmt, CppExpr> p = tcg.gen(def.getBody(), env);
			CppStmt ret = CppReturn.mk(p.snd());
			CppSeq.mk(p.fst(), ret).println(out, 1);
			out.println("}");
		}
		
	}

}
