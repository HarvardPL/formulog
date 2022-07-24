package edu.harvard.seas.pl.formulog.souffle.ast;

public class CInt implements CExpr {

    private final int n;

    public CInt(int n) {
        this.n = n;
    }

    @Override
    public String toString() {
        return Integer.toString(n);
    }

}
