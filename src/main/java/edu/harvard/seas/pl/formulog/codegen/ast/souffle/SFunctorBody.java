package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import edu.harvard.seas.pl.formulog.ast.Var;

import java.util.List;

public interface SFunctorBody {

    default int getArity() {
        return getArgs().size();
    }

    List<Var> getArgs();

    SType getRetType();

    boolean isStateful();

}
