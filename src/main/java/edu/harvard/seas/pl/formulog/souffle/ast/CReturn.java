package edu.harvard.seas.pl.formulog.souffle.ast;

public class CReturn implements CStmt {

    private final CExpr e;

    public CReturn(CExpr e_) {
        e = e_;
    }

    @Override
    public String toString() {
        return "return " + e + ";";
    }

}
