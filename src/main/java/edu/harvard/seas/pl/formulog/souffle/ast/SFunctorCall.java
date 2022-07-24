package edu.harvard.seas.pl.formulog.souffle.ast;

import java.util.List;

public class SFunctorCall implements STerm {

    private final String func;
    private final List<STerm> args;

    public SFunctorCall(String func_, List<STerm> args_) {
        func = func_;
        args = args_;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("@");
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
