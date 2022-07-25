package edu.harvard.seas.pl.formulog.codegen.ast.cpp;

import java.io.PrintWriter;

public class CppString implements CppExpr {

    private final String s;

    private CppString(String s) {
        this.s = s;
    }

    public static CppString mk(String s) {
        return new CppString(s);
    }

    @Override
    public void print(PrintWriter out) {
        out.print(this);
    }

    @Override
    public String toString() {
        return "\"" + s + "\"";
    }

}
