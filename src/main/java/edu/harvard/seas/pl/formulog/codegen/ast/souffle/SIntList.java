package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.List;

public class SIntList implements STerm {

    private final List<STerm> ts;

    public SIntList(List<STerm> ts_) {
        ts = ts_;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("[");
        for (int i = 0; i < ts.size(); ++i) {
            sb.append(ts.get(i));
            if (i < ts.size() - 1) {
                sb.append(", ");
            }
        }
        sb.append("]");
        return sb.toString();
    }

}
