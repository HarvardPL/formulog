package edu.harvard.seas.pl.formulog.souffle.ast;

public interface CExpr {

    default CStmt toStmt() {
        return new CStmt() {

            @Override
            public String toString() {
                return CExpr.this + ";";
            }

        };
    }

}
