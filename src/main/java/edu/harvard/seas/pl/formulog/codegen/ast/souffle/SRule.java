package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import java.util.List;

public class SRule {

    private final SLit head;
    private final List<SLit> body;

    public SRule(SLit head_, List<SLit> body_) {
        head = head_;
        body = body_;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(head);
        if (!body.isEmpty()) {
            sb.append(" :- ");
            for (int i = 0; i < body.size(); ++i) {
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
