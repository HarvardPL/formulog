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

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager.TupleSymbol;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Set;

public class SymbolCpp extends TemplateSrcFile {

    public SymbolCpp(CodeGenContext ctx) {
        super("Symbol.cpp", ctx);
    }

    public void gen(BufferedReader br, PrintWriter out) throws IOException {
        Worker w = new Worker(out);
        CodeGenUtil.copyOver(br, out, 0);
        w.defineSerialization();
        CodeGenUtil.copyOver(br, out, 1);
        w.initializeSymbolTable();
        CodeGenUtil.copyOver(br, out, 2);
        w.defineTupleLookup();
        CodeGenUtil.copyOver(br, out, -1);
    }

    private class Worker {

        private final Set<ConstructorSymbol> symbols = ctx.getConstructorSymbols();
        private final PrintWriter out;

        public Worker(PrintWriter out) {
            this.out = out;
        }

        void defineSerialization() {
            for (ConstructorSymbol sym : symbols) {
                out.print("    case ");
                out.print(ctx.lookupRepr(sym));
                out.print(": return out << \"");
                out.print(sym);
                out.println("\";");
            }
        }

        void initializeSymbolTable() {
            for (ConstructorSymbol sym : symbols) {
                CppExpr access = CppSubscript.mk(CppVar.mk("symbol_table"), CppConst.mkString(sym.toString()));
                CppExpr assign = CppBinop.mkAssign(access, CppVar.mk(ctx.lookupRepr(sym)));
                assign.toStmt().println(out, 1);
            }
        }

        void defineTupleLookup() {
            for (ConstructorSymbol sym : symbols) {
                if (sym instanceof TupleSymbol) {
                    out.print("    case " + sym.getArity() + ": return ");
                    out.print(ctx.lookupRepr(sym));
                    out.println(";");
                }
            }
        }

    }

}
