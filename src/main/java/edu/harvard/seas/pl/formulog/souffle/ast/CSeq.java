package edu.harvard.seas.pl.formulog.souffle.ast;

import java.util.Arrays;
import java.util.List;

public class CSeq implements CStmt {

    private final List<CStmt> stmts;

    public CSeq(List<CStmt> stmts) {
        this.stmts = stmts;
    }

    public CSeq(CStmt... stmts) {
        this(Arrays.asList(stmts));
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < stmts.size(); ++i) {
            String stmt = stmts.get(i).toString();
            sb.append(stmt);
            if (i < stmts.size() - 1 && !stmt.isEmpty()) {
                sb.append("\n");
            }
        }
        return sb.toString();
    }

}
