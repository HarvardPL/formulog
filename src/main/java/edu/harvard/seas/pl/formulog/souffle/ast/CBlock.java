package edu.harvard.seas.pl.formulog.souffle.ast;

public class CBlock implements CStmt {

    private final CStmt s;

    public CBlock(CStmt s_) {
        s = s_;
    }

    @Override
    public String toString() {
        return "{\n" + s + "\n}";
    }

}
