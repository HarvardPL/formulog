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
import java.util.ArrayList;
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public class TypeHpp {

	private final CodeGenContext ctx;

	public TypeHpp(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public void gen(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("Type.hpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("Type.hpp").toFile())) {
			Worker pr = new Worker(out);
			CodeGenUtil.copyOver(br, out, 0);
			pr.defineSymbolTypes();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}
	}

	private class Worker {

		private final PrintWriter out;
		private final TypeCodeGen tcg = new TypeCodeGen(ctx);

		public Worker(PrintWriter out) {
			this.out = out;
		}
		
		public void defineSymbolTypes() {
			for (ConstructorSymbol sym : ctx.getConstructorSymbols()) {
				defineSymbolType(sym);
			}
		}

		private void defineSymbolType(ConstructorSymbol sym) {
			out.println("    case " + ctx.lookupRepr(sym) + ": {");
			genCaseBody(sym).println(out, 3);
			out.println("    }");
		}
		
		private CppStmt genCaseBody(ConstructorSymbol sym) {
			List<CppStmt> acc = new ArrayList<>();
			FunctorType ft = simplify(sym.getCompileTimeType());
			List<CppExpr> argTypes = tcg.gen(acc, ft.getArgTypes());
			CppExpr retType = tcg.gen(acc, ft.getRetType());
			String vId = ctx.newId("v");
			acc.add(CppCtor.mkInitializer("vector<Type>", vId, argTypes));
			acc.add(CppReturn.mk(CppFuncCall.mk("make_pair", CppVar.mk(vId), retType)));
			return CppSeq.mk(acc);
		}
		
		private FunctorType simplify(FunctorType ft) {
			List<Type> args = new ArrayList<>();
			for (Type ty : ft.getArgTypes()) {
				args.add(TypeChecker.simplify(ty));
			}
			return new FunctorType(args, TypeChecker.simplify(ft.getRetType()));
		}

	}

}
