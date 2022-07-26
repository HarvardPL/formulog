package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.Arrays;
import java.util.List;

public class SRule {

    private final SLit head;
    private final List<SLit> body;

    public SRule(SLit head, List<SLit> body) {
        this.head = head;
        this.body = body;
    }

    public SRule(SLit head, SLit... body) {
        this(head, Arrays.asList(body));
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(head);
        if (!body.isEmpty()) {
            sb.append(" :- ");
            String sep = "";
            if (body.size() > 1) {
                sep = "\n\t";
            }
            for (int i = 0; i < body.size(); ++i) {
                sb.append(sep);
                sb.append(body.get(i));
                if (i < body.size() - 1) {
                    sb.append(", ");
                }
            }
        }
        sb.append(".");
        return sb.toString();
    }

}
