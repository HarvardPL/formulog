package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import edu.harvard.seas.pl.formulog.ast.Var;

public class SVar implements STerm {

    private final String name;

    public SVar(Var var) {
        String s = var.toString();
        if (s.charAt(0) == '$') {
            s = "x" + s.substring(1);
        }
        name = s;
    }

    @Override
    public String toString() {
        return name;
    }

}
