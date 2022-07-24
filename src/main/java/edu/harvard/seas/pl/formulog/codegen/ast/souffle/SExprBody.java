package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;

import java.util.List;

public class SExprBody implements SFunctorBody {

    private final List<Var> args;
    private final Term body;

    public SExprBody(List<Var> args_, Term body_) {
        args = args_;
        body = body_;
    }

    public Term getBody() {
        return body;
    }

    @Override
    public List<Var> getArgs() {
        return args;
    }

}
