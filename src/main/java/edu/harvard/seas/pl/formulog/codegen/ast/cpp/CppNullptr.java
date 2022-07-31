package edu.harvard.seas.pl.formulog.codegen.ast.cpp;

import java.io.PrintWriter;

public enum CppNullptr implements CppExpr {

    INSTANCE;

    @Override
    public void print(PrintWriter out) {
        out.print("nullptr");
    }

}
