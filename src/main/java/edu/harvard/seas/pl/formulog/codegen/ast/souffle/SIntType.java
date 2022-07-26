package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

public enum SIntType implements SType {
    INSTANCE;

    @Override
    public String toString() {
        return "number";
    }

}
