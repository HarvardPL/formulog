package edu.harvard.seas.pl.formulog.codegen;

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


import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.LiteralCodeGen.Result;
import edu.harvard.seas.pl.formulog.codegen.LiteralCodeGen.ResultType;
import edu.harvard.seas.pl.formulog.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.functions.PredicateFunctionDef;
import edu.harvard.seas.pl.formulog.functions.RecordAccessor;
import edu.harvard.seas.pl.formulog.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

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
		private final Set<PredicateFunctionSymbol> predFunctions = new HashSet<>();
		private final TermCodeGen tcg = new TermCodeGen(ctx);
		private final LiteralCodeGen lcg = new LiteralCodeGen(ctx);

		public Worker(PrintWriter out) {
			this.out = out;
		}

		private void makeDeclarations() {
			for (FunctionSymbol sym : ctx.getEval().getInputProgram().getFunctionSymbols()) {
				if (sym instanceof BuiltInFunctionSymbol) {
					registerBuiltInFunction((BuiltInFunctionSymbol) sym);
				} else if (sym instanceof PredicateFunctionSymbol) {
					predFunctions.add((PredicateFunctionSymbol) sym);
					declareFunction(sym);
				} else {
					FunctionDef def = ctx.getEval().getInputProgram().getDef(sym);
					if (def instanceof UserFunctionDef) {
						userDefinedFunctions.add(sym);
						declareFunction(sym);
					} else if (def instanceof RecordAccessor) {
						ctx.register(sym, "__access<" + ((RecordAccessor) def).getIndex() + ">");
					} else {
						throw new AssertionError("Unexpected function def: " + sym + " " + def.getClass());
					}
				}
			}
		}

		private void declareFunction(FunctionSymbol sym) {
			String name = CodeGenUtil.mkName(sym);
			ctx.register(sym, name);
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
				ctx.register(sym, "__add<float>");
				break;
			case FP32_DIV:
				ctx.register(sym, "__div<float>");
				break;
			case FP32_EQ:
				ctx.register(sym, "__eq<float>");
				break;
			case FP32_GE:
				ctx.register(sym, "__ge<float>");
				break;
			case FP32_GT:
				ctx.register(sym, "__gt<float>");
				break;
			case FP32_LE:
				ctx.register(sym, "__le<float>");
				break;
			case FP32_LT:
				ctx.register(sym, "__lt<float>");
				break;
			case FP32_MUL:
				ctx.register(sym, "__mul<float>");
				break;
			case FP32_NEG:
				ctx.register(sym, "__neg<float>");
				break;
			case FP32_REM:
				ctx.register(sym, "__rem<float>");
				break;
			case FP32_SUB:
				ctx.register(sym, "__sub<float>");
				break;
			case FP64_ADD:
				ctx.register(sym, "__add<double>");
				break;
			case FP64_DIV:
				ctx.register(sym, "__div<double>");
				break;
			case FP64_EQ:
				ctx.register(sym, "__eq<double>");
				break;
			case FP64_GE:
				ctx.register(sym, "__ge<double>");
				break;
			case FP64_GT:
				ctx.register(sym, "__gt<double>");
				break;
			case FP64_LE:
				ctx.register(sym, "__le<double>");
				break;
			case FP64_LT:
				ctx.register(sym, "__lt<double>");
				break;
			case FP64_MUL:
				ctx.register(sym, "__mul<double>");
				break;
			case FP64_NEG:
				ctx.register(sym, "__neg<double>");
				break;
			case FP64_REM:
				ctx.register(sym, "__rem<double>");
				break;
			case FP64_SUB:
				ctx.register(sym, "__sub<double>");
				break;
			case GET_MODEL:
				// XXX
				break;
			case I32_ADD:
				ctx.register(sym, "__add<int32_t>");
				break;
			case I32_AND:
				ctx.register(sym, "__bitwise_and<int32_t>");
				break;
			case I32_DIV:
				ctx.register(sym, "__div<int32_t>");
				break;
			case I32_GE:
				ctx.register(sym, "__ge<int32_t>");
				break;
			case I32_GT:
				ctx.register(sym, "__gt<int32_t>");
				break;
			case I32_LE:
				ctx.register(sym, "__le<int32_t>");
				break;
			case I32_LT:
				ctx.register(sym, "__lt<int32_t>");
				break;
			case I32_MUL:
				ctx.register(sym, "__mul<int32_t>");
				break;
			case I32_NEG:
				ctx.register(sym, "__neg<int32_t>");
				break;
			case I32_OR:
				ctx.register(sym, "__bitwise_or<int32_t>");
				break;
			case I32_REM:
				ctx.register(sym, "__rem<int32_t>");
				break;
			case I32_SCMP:
				ctx.register(sym, "__cmp<int32_t>");
				break;
			case I32_SUB:
				ctx.register(sym, "__sub<int32_t>");
				break;
			case I32_UCMP:
				ctx.register(sym, "__cmp<uint32_t>");
				break;
			case I32_XOR:
				ctx.register(sym, "__bitwise_xor<int32_t>");
				break;
			case I64_ADD:
				ctx.register(sym, "__add<int64_t>");
				break;
			case I64_AND:
				ctx.register(sym, "__bitwise_and<int64_t>");
				break;
			case I64_DIV:
				ctx.register(sym, "__div<int64_t>");
				break;
			case I64_GE:
				ctx.register(sym, "__ge<int64_t>");
				break;
			case I64_GT:
				ctx.register(sym, "__gt<int64_t>");
				break;
			case I64_LE:
				ctx.register(sym, "__le<int64_t>");
				break;
			case I64_LT:
				ctx.register(sym, "__lt<int64_t>");
				break;
			case I64_MUL:
				ctx.register(sym, "__mul<int64_t>");
				break;
			case I64_NEG:
				ctx.register(sym, "__neg<int64_t>");
				break;
			case I64_OR:
				ctx.register(sym, "__bitwise_or<int64_t>");
				break;
			case I64_REM:
				ctx.register(sym, "__rem<int64_t>");
				break;
			case I64_SCMP:
				ctx.register(sym, "__cmp<int64_t>");
				break;
			case I64_SUB:
				ctx.register(sym, "__sub<int64_t>");
				break;
			case I64_UCMP:
				ctx.register(sym, "__cmp<uint64_t>");
				break;
			case I64_XOR:
				ctx.register(sym, "__bitwise_xor<int64_t>");
				break;
			case IS_FREE:
				// XXX
				break;
			case IS_SAT:
				ctx.register(sym, "is_sat");
				break;
			case IS_SAT_OPT:
				ctx.register(sym, "is_sat_opt");
				break;
			case IS_VALID:
				ctx.register(sym, "is_valid");
				break;
			case PRINT:
				ctx.register(sym, "print");
				break;
			case QUERY_MODEL:
				// XXX
				break;
			case STRING_CONCAT:
				ctx.register(sym, "string_concat");
				break;
			case STRING_CMP:
				ctx.register(sym, "__cmp<string>");
				break;
			case STRING_MATCHES:
				ctx.register(sym, "string_matches");
				break;
			case STRING_STARTS_WITH:
				ctx.register(sym, "string_starts_with");
				break;
			case TO_STRING:
				ctx.register(sym, "to_string");
				break;
			case SUBSTITUTE:
				// XXX
				break;
			case fp32ToFp64:
				ctx.register(sym, "__conv<float, double>");
				break;
			case fp32ToI32:
				ctx.register(sym, "__conv<float, int32_t>");
				break;
			case fp32ToI64:
				ctx.register(sym, "__conv<float, int64_t>");
				break;
			case fp64ToFp32:
				ctx.register(sym, "__conv<double, float>");
				break;
			case fp64ToI32:
				ctx.register(sym, "__conv<double, int32_t>");
				break;
			case fp64ToI64:
				ctx.register(sym, "__conv<double, int64_t>");
				break;
			case i32ToFp32:
				ctx.register(sym, "__conv<int32_t, float>");
				break;
			case i32ToFp64:
				ctx.register(sym, "__conv<int32_t, double>");
				break;
			case i32ToI64:
				ctx.register(sym, "__conv<int32_t, int64_t>");
				break;
			case i64ToFp32:
				ctx.register(sym, "__conv<int64_t, float>");
				break;
			case i64ToFp64:
				ctx.register(sym, "__conv<int64_t, double>");
				break;
			case i64ToI32:
				ctx.register(sym, "__conv<int64_t, int32_t>");
				break;
			}
		}

		private void makeDefinitions() {
			for (FunctionSymbol sym : userDefinedFunctions) {
				makeDefinitionForUserDefinedFunc(sym);
			}
			for (PredicateFunctionSymbol funcSym : predFunctions) {
				makeDefinitionForPredFunc(funcSym);
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

		private void makeDefinitionForPredFunc(PredicateFunctionSymbol funcSym) {
			out.println();
			out.print("term_ptr " + ctx.lookupRepr(funcSym) + "(");
			RelationSymbol predSym = funcSym.getPredicateSymbol();
			int n = predSym.getArity();
			Term[] args = new Term[n];
			BindingType[] bindings = funcSym.getBindings();
			int j = 0;
			int nbound = nbound(bindings);
			Map<Var, CppExpr> env = new HashMap<>();
			for (int i = 0; i < n; ++i) {
				Var x = Var.fresh();
				args[i] = x;
				if (bindings[i].isBound()) {
					String id = ctx.newId("x");
					CppVar var = CppVar.mk(id);
					env.put(x, var);
					out.print("const term_ptr& ");
					var.print(out);
					if (j < nbound - 1) {
						out.print(", ");
					}
					j++;
				}
			}
			out.println(") {");
			PredicateFunctionDef def = getDef(funcSym);
			BindingType[] bindingsForIndex = def.getBindingsForIndex();
			SimplePredicate pred = SimplePredicate.make(predSym, args, bindingsForIndex, false);
			int index = def.getIndex();
			Result res = lcg.gen(pred, index, false, env);
			if (res.getResType() == ResultType.LOOKUP) {
				genLookup(res).println(out, 1);
			} else {
				pred = SimplePredicate.make(predSym, args, funcSym.getBindings(), false);
				genLoop(pred, res).println(out, 1);
			}
			out.println("}");
		}

		private PredicateFunctionDef getDef(PredicateFunctionSymbol sym) {
			DummyFunctionDef dummy = (DummyFunctionDef) ctx.getEval().getInputProgram().getDef(sym);
			PredicateFunctionDef def = (PredicateFunctionDef) dummy.getDef();
			assert def != null : sym;
			return def;
		}

		private CppStmt genLookup(Result res) {
			assert res.getResType() == ResultType.LOOKUP;
			CppStmt ifTrue = res.getK().apply(CppReturn.mk(CppFuncCall.mk("Term::make<bool>", CppConst.mkTrue())));
			return CppSeq.mk(ifTrue, CppReturn.mk(CppFuncCall.mk("Term::make<bool>", CppConst.mkFalse())));
		}

		private CppStmt genLoop(SimplePredicate pred, Result res) {
			assert res.getResType() == ResultType.LOOP;
			List<CppStmt> acc = new ArrayList<>();
			String listId = ctx.newId("list");
			CppExpr nil = tcg.mkComplex(acc, BuiltInConstructorSymbol.NIL);
			acc.add(CppDecl.mk(listId, nil));
			CppVar list = CppVar.mk(listId);
			CppStmt loopBody = genLoopBody(pred, res, list);
			acc.add(res.getK().apply(CppSeq.mk(loopBody)));
			acc.add(CppReturn.mk(list));
			return CppSeq.mk(acc);
		}

		private CppStmt genLoopBody(SimplePredicate pred, Result res, CppVar list) {
			List<CppStmt> body = new ArrayList<>();
			List<CppExpr> cols = tcg.gen(body, getFreeArgs(pred), res.getNewEnv());
			CppExpr tuple = genTuple(cols, body);
			CppExpr cons = tcg.mkComplex(body, BuiltInConstructorSymbol.CONS, tuple, list);
			body.add(CppBinop.mkAssign(list, cons).toStmt());
			return CppSeq.mk(body);
		}

		private CppExpr genTuple(List<CppExpr> args, List<CppStmt> acc) {
			int n = args.size();
			if (n == 1) {
				return args.get(0);
			} else {
				ConstructorSymbol sym = GlobalSymbolManager.lookupTupleSymbol(n);
				CppExpr tuple = tcg.mkComplex(acc, sym, args);
				String id = ctx.newId("t");
				acc.add(CppDecl.mk(id, tuple));
				return CppVar.mk(id);
			}
		}

		private int nbound(BindingType[] bindings) {
			int n = 0;
			for (BindingType binding : bindings) {
				if (binding.isBound()) {
					n++;
				}
			}
			return n;
		}

		private List<Term> getFreeArgs(SimplePredicate pred) {
			Term[] args = pred.getArgs();
			List<Term> freeArgs = new ArrayList<>();
			int i = 0;
			for (BindingType binding : pred.getBindingPattern()) {
				if (binding.isFree()) {
					freeArgs.add(args[i]);
				}
				i++;
			}
			return freeArgs;
		}

	}

}
