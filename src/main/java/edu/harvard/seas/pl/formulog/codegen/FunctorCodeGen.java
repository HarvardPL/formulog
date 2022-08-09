package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SDestructorBody;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SExprBody;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SFunctorBody;
import edu.harvard.seas.pl.formulog.util.Pair;

import java.io.*;
import java.util.*;

public class FunctorCodeGen {

    private final CodeGenContext ctx;

    private final static String headerName = "functors.h";
    private final static String sourceName = "functors.cpp";

    public FunctorCodeGen(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    public void emitFunctors(File directory) throws CodeGenException {
        emitHeader(directory);
        emitSource(directory);
    }

    private void emitHeader(File directory) throws CodeGenException {
        try (InputStream is = CodeGenUtil.inputSrcFile(headerName)) {
            assert is != null;
            File outHeader = CodeGenUtil.outputSrcFile(directory, headerName);
            try (InputStreamReader isr = new InputStreamReader(is);
                 BufferedReader br = new BufferedReader(isr);
                 PrintWriter out = new PrintWriter(outHeader)) {
                CodeGenUtil.copyOver(br, out, 0);
                for (Pair<String, SFunctorBody> p : ctx.getFunctors()) {
                    emitSignature(p.fst(), p.snd(), out);
                    out.println(";");
                }
                CodeGenUtil.copyOver(br, out, -1);
            }
        } catch (IOException e) {
            throw new CodeGenException(e);
        }
    }

    private Map<Var, CppVar> emitSignature(String functor, SFunctorBody body, PrintWriter out) {
        out.print("souffle::RamDomain ");
        out.print(functor);
        out.print("(");
        if (body.isStateful()) {
            out.print("souffle::SymbolTable *st, souffle::RecordTable *rt");
            if (body.getArity() > 0) {
                out.print(", ");
            }
        }
        List<Var> flgArgs = body.getArgs();
        Map<Var, CppVar> m = new LinkedHashMap<>();
        for (int i = 0; i < body.getArity(); ++i) {
            out.print("souffle::RamDomain ");
            String arg = "arg" + i;
            m.put(flgArgs.get(i), CppVar.mk(arg));
            out.print(arg);
            if (i < body.getArity() - 1) {
                out.print(", ");
            }
        }
        out.print(")");
        return m;
    }

    private void emitSource(File directory) throws CodeGenException {
        try (InputStream is = CodeGenUtil.inputSrcFile(sourceName)) {
            assert is != null;
            File outSource = CodeGenUtil.outputSrcFile(directory, sourceName);
            try (InputStreamReader isr = new InputStreamReader(is);
                 BufferedReader br = new BufferedReader(isr);
                 PrintWriter out = new PrintWriter(outSource)) {
                CodeGenUtil.copyOver(br, out, 0);
                new SourceWorker(out).emitFunctors();
                CodeGenUtil.copyOver(br, out, -1);
            }
        } catch (IOException e) {
            throw new CodeGenException(e);
        }
    }

    private class SourceWorker {

        private final PrintWriter out;

        public SourceWorker(PrintWriter out_) {
            out = out_;
        }

        public void emitFunctors() {
            for (Pair<String, SFunctorBody> p : ctx.getFunctors()) {
                emitFunctor(p.fst(), p.snd());
                out.println();
            }
        }

        private void emitFunctor(String functor, SFunctorBody body) {
            Map<Var, CppVar> params = emitSignature(functor, body, out);
            out.print(" ");
            Pair<CppStmt, Map<Var, CppExpr>> p1 = unpackParams(params);
            Pair<CppStmt, CppExpr> p2;
            if (body instanceof SExprBody) {
                p2 = genTermBody(((SExprBody) body).getBody(), p1.snd());
            } else {
                assert body instanceof SDestructorBody;
                p2 = genDtorBody((SDestructorBody) body, p1.snd());
            }
            CppStmt ret = CppReturn.mk(p2.snd());
            CppStmt block = CppBlock.mk(CppSeq.mk(p1.fst(), p2.fst(), ret));
            block.println(out, 0);
        }

        private Pair<CppStmt, Map<Var, CppExpr>> unpackParams(Map<Var, CppVar> params) {
            List<CppStmt> stmts = new ArrayList<>();
            Map<Var, CppExpr> env = new HashMap<>();
            for (Map.Entry<Var, CppVar> e : params.entrySet()) {
                String x = ctx.newId("x");
                CppExpr call = TermCodeGen.genUnintizeTerm(e.getValue());
                CppStmt stmt = CppDecl.mk(x, call);
                stmts.add(stmt);
                env.put(e.getKey(), CppVar.mk(x));
            }
            return new Pair<>(CppSeq.mk(stmts), env);
        }

        private Pair<CppStmt, CppExpr> genTermBody(Term t, Map<Var, CppExpr> env) {
            TermCodeGen tcg = new TermCodeGen(ctx);
            Pair<CppStmt, CppExpr> p = tcg.gen(t, env);
            CppExpr pack = TermCodeGen.genIntizeTerm(p.snd());
            return new Pair<>(p.fst(), pack);
        }

        private Pair<CppStmt, CppExpr> genDtorBody(SDestructorBody body, Map<Var, CppExpr> env) {
            Pair<CppStmt, CppExpr> p = new TermCodeGen(ctx).gen(body.getScrutinee(), env);
            String func = "dtor<" + ctx.lookupRepr(body.getSymbol()) + ">";
            CppExpr call = CppFuncCall.mk(func, p.snd());
            return new Pair<>(p.fst(), call);
        }

    }

}
