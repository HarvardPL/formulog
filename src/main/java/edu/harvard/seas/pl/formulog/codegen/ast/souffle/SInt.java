package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

public class SInt implements STerm {

    private final int val;

    public SInt(int val_) {
        val = val_;
    }

    @Override
    public String toString() {
        return Integer.toString(val);
    }

}
