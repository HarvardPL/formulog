package edu.harvard.seas.pl.formulog.souffle.ast;

public class CVar implements CExpr {

    private final String name;

    public CVar(String name_) {
        name = name_;
    }

    @Override
    public String toString() {
        return name;
    }

}
