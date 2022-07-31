package edu.harvard.seas.pl.formulog.codegen.ast.cpp;

import java.io.PrintWriter;
import java.util.List;

public class CppVectorLiteral implements CppExpr {

    private final List<CppExpr> elts;

    private CppVectorLiteral(List<CppExpr> elts) {
        this.elts = elts;
    }

    public static CppVectorLiteral mk(List<CppExpr> elts) {
        return new CppVectorLiteral(elts);
    }

    @Override
    public void print(PrintWriter out) {
        out.print("{");
        for (int i = 0; i < elts.size(); ++i) {
            out.print(elts.get(i));
            if (i < elts.size() - 1) {
                out.print(", ");
            }
        }
        out.print("}");
    }

}
