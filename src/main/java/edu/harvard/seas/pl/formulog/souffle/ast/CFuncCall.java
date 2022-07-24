package edu.harvard.seas.pl.formulog.souffle.ast;

import java.util.Arrays;
import java.util.List;

public class CFuncCall implements CExpr {

    private final String func;
    private final List<CExpr> args;

    public CFuncCall(String func_, List<CExpr> args_) {
        func = func_;
        args = args_;
    }

    public CFuncCall(String func_, CExpr... args_) {
        func = func_;
        args = Arrays.asList(args_);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(func);
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
