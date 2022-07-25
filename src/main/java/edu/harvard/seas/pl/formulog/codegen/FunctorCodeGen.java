package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.CppVar;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SDestructorBody;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SFunctorBody;
import edu.harvard.seas.pl.formulog.souffle.SouffleGenUtil;
import edu.harvard.seas.pl.formulog.util.Pair;

import java.io.*;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
        if (body instanceof SDestructorBody) {
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
            /*
            for (Pair<String, SFunctorBody> p : ctx.getFunctors()) {
                emitFunctor(p.fst(), p.snd());
                out.println();
            }
             */
        }

        /*
        private void emitFunctor(String functor, SFunctorBody body) {
            Map<Var, CVar> params = emitSignature(functor, body, out);
            out.print(" ");
            Pair<CStmt, FunctionContext> p1 = unpackParams(params);
            Pair<CStmt, CExpr> p2;
            if (body instanceof SExprBody) {
                p2 = genTermBody(((SExprBody) body).getBody(), p1.snd());
            } else {
                assert body instanceof SDestructorBody;
                p2 = new Pair<>(new CSeq(), new CInt(42));
            }
            CStmt ret = new CReturn(p2.snd());
            CStmt block = new CBlock(new CSeq(p1.fst(), p2.fst(), ret));
            out.println(block);
        }

        private Pair<CStmt, FunctionContext> unpackParams(Map<Var, CVar> params) {
            FunctionContext funcCtx = new FunctionContext();
            List<CStmt> stmts = new ArrayList<>();
            for (Map.Entry<Var, CVar> e : params.entrySet()) {
                CVar x = funcCtx.lookupOrCreate(e.getKey());
                CExpr call = new CFuncCall("formulog::Term::unintize", e.getValue());
                CStmt stmt = new CAssign(x, call, true);
                stmts.add(stmt);
            }
            return new Pair<>(new CSeq(stmts), funcCtx);
        }

        private Pair<CStmt, CExpr> genTermBody(Term t, FunctionContext funcCtx) {
            TermTranslator termTranslator = new TermTranslator(ctx, funcCtx);
            Pair<CStmt, CExpr> p = termTranslator.translate(t);
            CExpr pack = new CFuncCall("formulog::Term::intize", p.snd());
            return new Pair<>(p.fst(), pack);
        }

         */
    }

}
