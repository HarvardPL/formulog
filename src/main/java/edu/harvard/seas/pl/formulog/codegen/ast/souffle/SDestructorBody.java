package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;

import java.util.List;

public class SDestructorBody implements SFunctorBody {

    private final List<Var> args;
    private final Term scrutinee;
    private final ConstructorSymbol symbol;

    public SDestructorBody(List<Var> args_, Term scrutinee_, ConstructorSymbol symbol_) {
        args = args_;
        scrutinee = scrutinee_;
        symbol = symbol_;
    }

    @Override
    public List<Var> getArgs() {
        return args;
    }

    public Term getScrutinee() {
        return scrutinee;
    }

    public ConstructorSymbol getSymbol() {
        return symbol;
    }

}
