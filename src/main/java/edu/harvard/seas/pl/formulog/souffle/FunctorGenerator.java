package edu.harvard.seas.pl.formulog.souffle;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.souffle.ast.*;
import edu.harvard.seas.pl.formulog.util.Pair;

import java.io.*;
import java.util.*;

public class FunctorGenerator {

    private final BasicProgram prog;
    private final Context ctx;

    private final static String headerName = "functors.h";
    private final static String sourceName = "functors.cpp";

    public FunctorGenerator(BasicProgram prog_, Context ctx_) {
        prog = prog_;
        ctx = ctx_;
    }

    public void emitFunctors(File directory) throws SouffleGenException {
        emitHeader(directory);
        emitSource(directory);
    }

    private void emitHeader(File directory) throws SouffleGenException {
        File inHeader = new File("souffle").toPath().resolve("src").resolve(headerName).toFile();
        File outHeader = directory.toPath().resolve(headerName).toFile();
        try (InputStream is = getClass().getClassLoader().getResourceAsStream(inHeader.getPath())) {
            assert is != null;
            try (InputStreamReader isr = new InputStreamReader(is);
                 BufferedReader br = new BufferedReader(isr);
                 PrintWriter out = new PrintWriter(outHeader)) {
                SouffleGenUtil.copyOverUntilInsertPoint(br, out);
                for (Pair<String, SFunctorBody> p : ctx.getFunctors()) {
                    emitSignature(p.fst(), p.snd(), out);
                    out.println(";");
                }
                SouffleGenUtil.copyOverUntilInsertPoint(br, out);
            }
        } catch (IOException e) {
            throw new SouffleGenException(e);
        }
    }

    private Map<Var, CVar> emitSignature(String functor, SFunctorBody body, PrintWriter out) {
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
        Map<Var, CVar> m = new LinkedHashMap<>();
        for (int i = 0; i < body.getArity(); ++i) {
            out.print("souffle::RamDomain ");
            String arg = "arg" + i;
            m.put(flgArgs.get(i), new CVar(arg));
            out.print(arg);
            if (i < body.getArity() - 1) {
                out.print(", ");
            }
        }
        out.print(")");
        return m;
    }

    private void emitSource(File directory) throws SouffleGenException {
        File inSource = new File("souffle").toPath().resolve("src").resolve(sourceName).toFile();
        File outSource = directory.toPath().resolve(sourceName).toFile();
        try (InputStream is = getClass().getClassLoader().getResourceAsStream(inSource.getPath())) {
            assert is != null;
            try (InputStreamReader isr = new InputStreamReader(is);
                 BufferedReader br = new BufferedReader(isr);
                 PrintWriter out = new PrintWriter(outSource)) {
                SouffleGenUtil.copyOverUntilInsertPoint(br, out);
                new SourceWorker(out).emitFunctors();
            }
        } catch (IOException e) {
            throw new SouffleGenException(e);
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

    }

}
