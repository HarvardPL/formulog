package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2023 President and Fellows of Harvard College
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
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppBinop;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppConst;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppDecl;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppExpr;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppExprFromString;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppFuncCall;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppIf;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppMethodCall;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppReturn;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppSeq;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppStmt;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppVar;
import edu.harvard.seas.pl.formulog.smt.SmtLibParser;
import edu.harvard.seas.pl.formulog.smt.SmtLibParser.SmtLibParseException;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Pair;

public class SmtParserCpp extends TemplateSrcFile {

    public SmtParserCpp(CodeGenContext ctx) {
        super("smt_parser.cpp", ctx);
    }

    @Override
    void gen(BufferedReader br, PrintWriter out) throws IOException, CodeGenException {
        Worker w = new Worker(out);
        CodeGenUtil.copyOver(br, out, 0);
        w.outputShouldRecord();
        CodeGenUtil.copyOver(br, out, 1);
        w.outputParseFuncs();
        CodeGenUtil.copyOver(br, out, 2);
        w.outputParseTerm();
        CodeGenUtil.copyOver(br, out, -1);
    }

    private class Worker {

        private final PrintWriter out;
        private final Set<ConstructorSymbol> trackedSmtVars = new HashSet<>();
        private final Map<Type, String> parseFuncs = new HashMap<>();
        private final Map<String, CppStmt> parseFuncDefs = new HashMap<>();

        public Worker(PrintWriter out) {
            this.out = out;
            parseFuncs.put(BuiltInTypes.string, "parse_string");
            parseFuncs.put(BuiltInTypes.i32, "parse_i32");
            parseFuncs.put(BuiltInTypes.i64, "parse_i64");
            parseFuncs.put(BuiltInTypes.fp32, "parse_fp32");
            parseFuncs.put(BuiltInTypes.fp64, "parse_fp64");
            parseFuncs.put(BuiltInTypes.bool, "parse_bool");

        }

        private void outputShouldRecord() throws CodeGenException {
            for (ConstructorSymbol sym : ctx.getConstructorSymbols()) {
                var ty = getSmtVarType(sym);
                if (ty != null) {
                    try {
                        if (SmtLibParser.shouldRecord(ty)) {
                            out.printf("    case %s: return true;\n", ctx.lookupRepr(sym));
                            trackedSmtVars.add(sym);
                        }
                    } catch (SmtLibParseException e) {
                        throw new CodeGenException(e);
                    }
                }
            }
        }

        private void outputParseFuncs() {
            for (ConstructorSymbol sym : trackedSmtVars) {
                genParseFunc(getSmtVarType(sym));
            }
            // Forward-declare functions to account for mutually recursive data types.
            for (String name : parseFuncDefs.keySet()) {
                out.println("struct " + name + ";");
            }
            out.println();
            for (Map.Entry<String, CppStmt> e : parseFuncDefs.entrySet()) {
                out.println("struct " + e.getKey() + " {");
                out.println("  term_ptr operator()(SmtLibTokenizer &t) {");
                e.getValue().println(out, 2);
                out.println("  }\n};\n");
            }
        }

        private String genParseFunc(AlgebraicDataType ty) {
            String name = parseFuncs.get(ty);
            if (name != null) {
                return name;
            }
            name = "parse_" + ctx.newId(CodeGenUtil.mkName(ty.getSymbol()));
            var wrapped_name = "parse_adt<" + name + ">";
            parseFuncs.put(ty, wrapped_name);

            List<CppStmt> body = new ArrayList<>();
            String scrutinee = "x";
            body.add(CppDecl.mk(scrutinee, CppFuncCall.mk("parse_identifier", CppVar.mk("t"))));

            List<Pair<CppExpr, CppStmt>> cases = new ArrayList<>();
            for (var cs : ty.getConstructors()) {
                cases.add(genConstructorCase(CppVar.mk(scrutinee), cs));
            }
            body.add(CppIf.mk(cases));

            body.add(CppExprFromString.mk("abort()").toStmt());
            parseFuncDefs.put(name, CppSeq.mk(body));
            return wrapped_name;
        }

        private Pair<CppExpr, CppStmt> genConstructorCase(CppExpr scrutinee, ConstructorScheme cs) {
            ConstructorSymbol sym = cs.getSymbol();
            var check = CppBinop.mkEq(scrutinee, CppConst.mkString(sym.toString()));
            List<CppExpr> args = new ArrayList<>();
            List<CppStmt> stmts = new ArrayList<>();
            int i = 0;
            for (var ty : cs.getTypeArgs()) {
                String arg = "a" + i;
                CppStmt decl = CppDecl.mk(arg, CppFuncCall.mk(genParseFunc((AlgebraicDataType) ty), CppVar.mk("t")));
                stmts.add(decl);
                args.add(CppVar.mk(arg));
                i++;
            }
            CppExpr term = CppFuncCall.mk("Term::make<" + ctx.lookupRepr(sym) + ">", args); 
            stmts.add(CppReturn.mk(term));
            return new Pair<>(check, CppSeq.mk(stmts));
        }

        private void outputParseTerm() {
            for (ConstructorSymbol sym : trackedSmtVars) {
                var ty = getSmtVarType(sym);
                var func = parseFuncs.get(ty);
                out.printf("    case %s: return %s(t);\n", ctx.lookupRepr(sym), func);
            }
        }

        private AlgebraicDataType getSmtVarType(ConstructorSymbol sym) {
            if (sym instanceof ParameterizedConstructorSymbol) {
                var base = ((ParameterizedConstructorSymbol) sym).getBase();
                if (base.equals(BuiltInConstructorSymbolBase.SMT_VAR)) {
                    return SmtLibParser.stripSymType((AlgebraicDataType) sym.getCompileTimeType().getRetType());
                }
            }
            return null;
        }

    }

}
