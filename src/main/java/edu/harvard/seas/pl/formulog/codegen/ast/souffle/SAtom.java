package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.List;

public class SAtom implements SLit {

    private final String pred;
    private final List<STerm> args;
    private final boolean isNegated;

    public SAtom(String symbol_, List<STerm> args_, boolean isNegated_) {
        pred = symbol_;
        args = args_;
        isNegated = isNegated_;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (isNegated) {
            sb.append("!");
        }
        sb.append(pred);
        sb.append("(");
        for (int i = 0; i < args.size(); ++i) {
            sb.append(args.get(i));
            if (i < args.size() - 1) {
                sb.append(", ");
            }
        }
        sb.append(")");
        return sb.toString();
    }

}
