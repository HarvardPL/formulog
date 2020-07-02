package edu.harvard.seas.pl.formulog.eval;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.FunctionDefValidation;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

import java.util.Set;

public class BalbinEvaluation implements Evaluation {

    private final UserPredicate query;
    private final WellTypedProgram inputProgram;

    @SuppressWarnings("serial")
    public static BalbinEvaluation setup(WellTypedProgram prog)
            throws InvalidProgramException {
        FunctionDefValidation.validate(prog);
        MagicSetTransformer mst = new MagicSetTransformer(prog);

        // TODO: define a new transform function here
        BasicProgram magicProg = mst.transform(Configuration.useDemandTransformation, true);
//        Set<RelationSymbol> allRelations = new HashSet<>(magicProg.getFactSymbols());
//        allRelations.addAll(magicProg.getRuleSymbols());

        //        Set<BasicRule> db = new HashSet<>();
//        for (RelationSymbol ruleSymbol : magicProg.getRuleSymbols()) {
//            db.addAll(magicProg.getRules(ruleSymbol));
//        }

        // TODO: part 5 - setup for part 6:
        // x create a pred(p) function
        // - create a prules(q, D) function that takes a predicate q, database D, and returns a set of rules (a subset of D)

        // Definition 29 - prules:
        // Create a dependency graph for running prules

        return new BalbinEvaluation(prog, magicProg.getQuery());
    }

    // Balbin, Definition 1 - pred(p)
    private static UserPredicate getPred(ComplexLiteral p) {
        return p.accept(new ComplexLiterals.ComplexLiteralVisitor<Void, UserPredicate>() {

            @Override
            public UserPredicate visit(UnificationPredicate unificationPredicate, Void input) {
                return null;
            }

            @Override
            public UserPredicate visit(UserPredicate userPredicate, Void input) {
                return userPredicate;
            }

        }, null);
    }

//    private static Set<BasicRule> getPRules(RelationSymbol q, Set<BasicRule> db) {
//        Set<BasicRule> prules = new HashSet<>();
//
//        // Case 1 - q = pred(p0), where p0 is the head of a rule
//
//        // Case 2 - q <--(+) pred(p0), where p0 is the head of a rule
//
//        return prules;
//    }

    BalbinEvaluation(WellTypedProgram inputProgram, UserPredicate query) {
        this.inputProgram = inputProgram;
        this.query = query;
    }

    @Override
    public void run() throws EvaluationException {

    }

    @Override
    public EvaluationResult getResult() {
        return null;
    }

    @Override
    public boolean hasQuery() {
        return false;
    }

    @Override
    public UserPredicate getQuery() {
        return null;
    }

    @Override
    public WellTypedProgram getInputProgram() {
        return inputProgram;
    }

}
