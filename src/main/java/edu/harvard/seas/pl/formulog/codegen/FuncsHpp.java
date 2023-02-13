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


import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.functions.*;
import edu.harvard.seas.pl.formulog.symbols.*;
import edu.harvard.seas.pl.formulog.util.Pair;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.stream.Collectors;

public class FuncsHpp extends TemplateSrcFile {

    public FuncsHpp(CodeGenContext ctx) {
        super("funcs.hpp", ctx);
    }

    public void gen(BufferedReader br, PrintWriter out) throws IOException {
        Worker pr = new Worker(out);
        CodeGenUtil.copyOver(br, out, 0);
        pr.makeDeclarations();
        CodeGenUtil.copyOver(br, out, 1);
        pr.makeDefinitions();
        CodeGenUtil.copyOver(br, out, -1);
    }

    private class Worker {

        private final PrintWriter out;
        private final Set<FunctionSymbol> userDefinedFunctions = new HashSet<>();
        private final Set<PredicateFunctionSymbol> predFunctions = new HashSet<>();
        private final TermCodeGen tcg = new TermCodeGen(ctx);

        public Worker(PrintWriter out) {
            this.out = out;
        }

        private void makeDeclarations() {
            for (FunctionSymbol sym : ctx.getProgram().getFunctionSymbols()) {
                if (sym instanceof BuiltInFunctionSymbol) {
                    registerBuiltInFunction((BuiltInFunctionSymbol) sym);
                } else if (sym instanceof PredicateFunctionSymbol) {
                    predFunctions.add((PredicateFunctionSymbol) sym);
                    declareFunction(sym);
                } else {
                    FunctionDef def = ctx.getProgram().getDef(sym);
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
                out.print("term_ptr");
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
                case I32_ADD:
                    ctx.register(sym, "__add<int32_t>");
                    break;
                case I32_AND:
                    ctx.register(sym, "__bitwise_and<int32_t>");
                    break;
                case I32_SDIV:
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
                case I32_SREM:
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
                case I32_SHL:
                    ctx.register(sym, "__shl<int32_t>");
                    break;
                case I32_ASHR:
                    ctx.register(sym, "__ashr<int32_t>");
                    break;
                case I32_LSHR:
                    ctx.register(sym, "__lshr<int32_t, uint32_t>");
                    break;
                case I32_UREM:
                    ctx.register(sym, "__urem<int32_t, uint32_t>");
                    break;
                case I32_UDIV:
                    ctx.register(sym, "__udiv<int32_t, uint32_t>");
                    break;
                case I64_ADD:
                    ctx.register(sym, "__add<int64_t>");
                    break;
                case I64_AND:
                    ctx.register(sym, "__bitwise_and<int64_t>");
                    break;
                case I64_SDIV:
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
                case I64_SREM:
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
                case I64_SHL:
                    ctx.register(sym, "__shl<int64_t>");
                    break;
                case I64_ASHR:
                    ctx.register(sym, "__ashr<int64_t>");
                    break;
                case I64_LSHR:
                    ctx.register(sym, "__lshr<int64_t, uint64_t>");
                    break;
                case I64_UREM:
                    ctx.register(sym, "__urem<int64_t, uint64_t>");
                    break;
                case I64_UDIV:
                    ctx.register(sym, "__udiv<int64_t, uint64_t>");
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
                case GET_MODEL:
                    ctx.register(sym, "get_model");
                    break;
                case QUERY_MODEL:
                    ctx.register(sym, "query_model");
                    break;
                case PRINT:
                    ctx.register(sym, "print");
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
                case CHAR_AT:
                    ctx.register(sym, "char_at");
                    break;
                case STRING_LENGTH:
                    ctx.register(sym, "string_length");
                    break;
                case STRING_TO_LIST:
                    ctx.register(sym, "string_to_list");
                    break;
                case LIST_TO_STRING:
                    ctx.register(sym, "list_to_string");
                    break;
                case SUBSTRING:
                    ctx.register(sym, "substring");
                    break;
                case stringToI32:
                    ctx.register(sym, "string_to_i32");
                    break;
                case stringToI64:
                    ctx.register(sym, "string_to_i64");
                    break;
                case OPAQUE_SET_EMPTY:
                    ctx.register(sym, "opaque_set_empty");
                    break;
                case OPAQUE_SET_PLUS:
                    ctx.register(sym, "opaque_set_plus");
                    break;
                case OPAQUE_SET_MINUS:
                    ctx.register(sym, "opaque_set_minus");
                    break;
                case OPAQUE_SET_UNION:
                    ctx.register(sym, "opaque_set_union");
                    break;
                case OPAQUE_SET_DIFF:
                    ctx.register(sym, "opaque_set_diff");
                    break;
                case OPAQUE_SET_CHOOSE:
                    ctx.register(sym, "opaque_set_choose");
                    break;
                case OPAQUE_SET_SIZE:
                    ctx.register(sym, "opaque_set_size");
                    break;
                case OPAQUE_SET_MEMBER:
                    ctx.register(sym, "opaque_set_member");
                    break;
                case OPAQUE_SET_SINGLETON:
                    ctx.register(sym, "opaque_set_singleton");
                    break;
                case OPAQUE_SET_SUBSET:
                    ctx.register(sym, "opaque_set_subset");
                    break;
                case OPAQUE_SET_FROM_LIST:
                    ctx.register(sym, "opaque_set_from_list");
                    break;
                case IS_SET_SAT:
                    ctx.register(sym, "is_set_sat");
                    break;
                default:
                    throw new AssertionError("unhandled built-in function symbol: " + sym);
            }
        }

        private void makeDefinitions() {
            var sorted = userDefinedFunctions.stream().sorted(Comparator.comparing(Object::toString)).collect(Collectors.toList());
            for (FunctionSymbol sym : sorted) {
                makeDefinitionForUserDefinedFunc(sym);
            }
            for (PredicateFunctionSymbol funcSym : predFunctions) {
                makeDefinitionForPredFunc(funcSym);
            }
        }

        private void makeDefinitionForUserDefinedFunc(FunctionSymbol sym) {
            UserFunctionDef def = (UserFunctionDef) ctx.getProgram().getDef(sym);
            out.println();
            out.print("term_ptr " + ctx.lookupRepr(sym) + "(");
            Map<Var, CppExpr> env = new HashMap<>();
            Iterator<Var> params = def.getParams().iterator();
            int n = sym.getArity();
            List<String> cppParams = new ArrayList<>();
            for (int i = 0; i < n; ++i) {
                String id = ctx.newId("x");
                CppVar var = CppVar.mk(id);
                env.put(params.next(), var);
                out.print("term_ptr ");
                var.print(out);
                if (i < n - 1) {
                    out.print(", ");
                }
                cppParams.add(var.toString());
            }
            out.println(") {");
            if (n == 0) {
                out.println("  static std::atomic<term_ptr> memo{nullptr};");
                out.println("  if (memo) { return memo; }");
            } else {
                if (n == 1) {
                    out.println("  typedef term_ptr Key;");
                    out.println("  Key key = " + cppParams.get(0) + ";");
                } else {
                    out.println("  typedef std::array<term_ptr, " + n + "> Key;");
                    out.println("  Key key = {" + String.join(", ", cppParams) + "};");
                }
                out.println("  static tbb::concurrent_unordered_map<Key, term_ptr, boost::hash<Key>> memo;");
                out.println("  auto it = memo.find(key);");
                out.println("  if (it != memo.end()) { return it->second; }");
            }
            Pair<CppStmt, CppExpr> p = tcg.gen(def.getBody(), env);
            p.fst().println(out, 1);
            String retVar = ctx.newId("ret");
            CppDecl.mk(retVar, p.snd()).println(out, 1);
            if (n == 0) {
                out.println("  memo = " + retVar + ";");
            } else {
                out.println("  memo.emplace(key, " + retVar + ");");
            }
            CppReturn.mk(CppVar.mk(retVar)).println(out, 1);
            out.println("}");
        }

        private void makeDefinitionForPredFunc(PredicateFunctionSymbol funcSym) {
            out.println();
            out.print("term_ptr " + ctx.lookupRepr(funcSym) + "(");
            RelationSymbol predSym = funcSym.getPredicateSymbol();
            int n = predSym.getArity();
            BindingType[] bindings = funcSym.getBindings();
            int j = 0;
            int nbound = numBound(bindings);
            List<Integer> free = new ArrayList<>();
            boolean hasIgnored = false;
            CppVar[] args = new CppVar[bindings.length];
            for (int i = 0; i < n; ++i) {
                if (bindings[i].isBound()) {
                    String id = ctx.newId("x");
                    CppVar var = CppVar.mk(id);
                    args[i] = var;
                    out.print("term_ptr ");
                    var.print(out);
                    if (j < nbound - 1) {
                        out.print(", ");
                    }
                    j++;
                } else if (bindings[i].isFree()) {
                    free.add(i);
                } else if (bindings[i].isIgnored()) {
                    hasIgnored = true;
                }
            }
            if (hasIgnored) {
                System.err.println("WARNING: relation query " + funcSym + " has ignored attribute; this might lead to slow performance");
            }
            out.println(") ");
            Pair<CppStmt, CppExpr> p;
            if (free.isEmpty()) {
                p = genRelationContains(predSym, args, hasIgnored);
            } else if (free.size() == 1) {
                p = genRelationAggMono(predSym, args, free.get(0));
            } else {
                p = genRelationAggPoly(predSym, args, free);
            }
            CppStmt ret = CppReturn.mk(p.snd());
            CppBlock.mk(CppSeq.mk(p.fst(), ret)).println(out, 0);
        }

        private CppExpr mkArgsVec(CppVar[] args) {
            var cppArgs = Arrays.stream(args).map(x -> x == null ? CppNullptr.INSTANCE : x).collect(Collectors.toList());
            return CppVectorLiteral.mk(cppArgs);
        }

        private Pair<CppStmt, CppExpr> genRelationAggMono(RelationSymbol predSym, CppVar[] args, int pos) {
            CppExpr name = CppConst.mkString(ctx.lookupRepr(predSym));
            CppExpr vec = mkArgsVec(args);
            CppExpr call = CppFuncCall.mk("_relation_agg_mono", name, vec, CppConst.mkInt(pos));
            return new Pair<>(CppSeq.skip(), call);
        }

        private Pair<CppStmt, CppExpr> genRelationAggPoly(RelationSymbol predSym, CppVar[] args, List<Integer> free) {
            CppExpr name = CppConst.mkString(ctx.lookupRepr(predSym));
            CppExpr vec = mkArgsVec(args);
            List<CppExpr> projection = new ArrayList<>();
            int pos = 0;
            for (int i = 0; i < predSym.getArity(); ++i) {
                if (i == free.get(pos)) {
                    projection.add(CppConst.mkTrue());
                    pos++;
                } else {
                    projection.add(CppConst.mkFalse());
                }
            }
            assert pos == free.size();
            ConstructorSymbol tupleSym = GlobalSymbolManager.lookupTupleSymbol(free.size());
            String funcName = "_relation_agg_poly<" + ctx.lookupRepr(tupleSym) + ">";
            CppExpr call = CppFuncCall.mk(funcName, name, vec, CppVectorLiteral.mk(projection));
            return new Pair<>(CppSeq.skip(), call);
        }

        private Pair<CppStmt, CppExpr> genRelationContains(RelationSymbol predSym, CppVar[] args, boolean hasIgnored) {
            CppExpr name = CppConst.mkString(ctx.lookupRepr(predSym));
            CppExpr vec = mkArgsVec(args);
            String func;
            if (hasIgnored) {
                func = "_relation_contains";
            } else {
                func = "_relation_contains_complete";
            }
            CppExpr call = CppFuncCall.mk(func, name, vec);
            return new Pair<>(CppSeq.skip(), call);
        }

        private int numBound(BindingType[] bindings) {
            int n = 0;
            for (BindingType binding : bindings) {
                if (binding.isBound()) {
                    n++;
                }
            }
            return n;
        }

    }

}
