package edu.harvard.seas.pl.formulog.souffle;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.souffle.ast.CExpr;
import edu.harvard.seas.pl.formulog.souffle.ast.CInt;
import edu.harvard.seas.pl.formulog.souffle.ast.CSeq;
import edu.harvard.seas.pl.formulog.souffle.ast.CStmt;
import edu.harvard.seas.pl.formulog.util.Pair;

import java.util.Collections;

public class TermTranslator {

    private final Context ctx;
    private final FunctionContext funcCtx;

    public TermTranslator(Context ctx, FunctionContext funcCtx) {
        this.ctx = ctx;
        this.funcCtx = funcCtx;
    }

    public Pair<CStmt, CExpr> translate(Term t) {
        return new Pair<>(new CSeq(), new CInt(0));
    }

}
