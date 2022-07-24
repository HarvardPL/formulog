package edu.harvard.seas.pl.formulog.souffle.ast;

public class SInfixBinaryOpAtom implements SLit {

    private final STerm lhs;
    private final String op;
    private final STerm rhs;

    public SInfixBinaryOpAtom(STerm lhs_, String op_, STerm rhs_) {
        lhs = lhs_;
        op = op_;
        rhs = rhs_;
    }

    @Override
    public String toString() {
        return lhs + " " + op + " " + rhs;
    }

}
