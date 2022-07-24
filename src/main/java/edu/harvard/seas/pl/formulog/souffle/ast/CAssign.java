package edu.harvard.seas.pl.formulog.souffle.ast;

public class CAssign implements CStmt {

    private final CVar def;
    private final CExpr val;
    private final boolean isRef;

    public CAssign(CVar def, CExpr val, boolean isRef) {
        this.def = def;
        this.val = val;
        this.isRef = isRef;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("auto ");
        if (isRef) {
            sb.append("&");
        }
        sb.append(def);
        sb.append(" = ");
        sb.append(val);
        sb.append(";");
        return sb.toString();
    }
}
