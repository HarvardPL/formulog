package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.Objects;

public class SIntListType implements SType {

    private final int arity;

    public SIntListType(int arity) {
        this.arity = arity;
    }

    public String getName() {
        return "IntList" + arity;
    }

    public String getDef() {
        StringBuilder sb = new StringBuilder();
        sb.append("[");
        for (int i = 0; i < arity; ++i) {
            sb.append("x");
            sb.append(i);
            sb.append(":number");
            if (i < arity - 1) {
                sb.append(", ");
            }
        }
        sb.append("]");
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SIntListType that = (SIntListType) o;
        return arity == that.arity;
    }

    @Override
    public int hashCode() {
        return Objects.hash(arity);
    }

    @Override
    public String toString() {
        return getName();
    }

}
