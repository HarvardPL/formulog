package edu.harvard.seas.pl.formulog.souffle.ast;

import edu.harvard.seas.pl.formulog.ast.Var;

import java.util.List;

public interface SFunctorBody {

    default int getArity() {
        return getArgs().size();
    }

    List<Var> getArgs();

}
