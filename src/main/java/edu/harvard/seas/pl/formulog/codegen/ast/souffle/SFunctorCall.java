package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.Arrays;
import java.util.List;

public class SFunctorCall implements STerm {

    private final String func;
    private final List<STerm> args;

    public SFunctorCall(String func, List<STerm> args) {
        this.func = func;
        this.args = args;
    }

    public SFunctorCall(String func, STerm... args) {
        this(func, Arrays.asList(args));
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
