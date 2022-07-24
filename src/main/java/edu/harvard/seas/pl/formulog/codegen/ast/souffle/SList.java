package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.List;

public class SList implements STerm {

    private final List<STerm> ts;

    public SList(List<STerm> ts_) {
        ts = ts_;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (STerm t : ts) {
            sb.append("[");
            sb.append(t);
            sb.append(", ");
        }
        sb.append("nil");
        for (STerm _t : ts) {
            sb.append("]");
        }
        return sb.toString();
    }

}
