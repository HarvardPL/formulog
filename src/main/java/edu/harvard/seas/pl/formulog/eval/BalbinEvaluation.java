package edu.harvard.seas.pl.formulog.eval;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.codegen.Relation;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.validating.FunctionDefValidation;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import org.jgrapht.Graph;
import org.jgrapht.GraphPath;
import org.jgrapht.alg.shortestpath.AllDirectedPaths;
import org.jgrapht.graph.DefaultDirectedGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class BalbinEvaluation implements Evaluation {

//    public static void main(String[] args) {
//        System.out.println("Hello World!");
//    }

    private final UserPredicate query;
    private final WellTypedProgram inputProgram;

    @SuppressWarnings("serial")
    public static BalbinEvaluation setup(WellTypedProgram prog)
            throws InvalidProgramException {
        FunctionDefValidation.validate(prog);
        MagicSetTransformer mst = new MagicSetTransformer(prog);

        BasicProgram magicProg = mst.transform(Configuration.useDemandTransformation,
                MagicSetTransformer.RestoreStratification.FALSE_AND_NO_MAGIC_RULES_FOR_NEG_LITERALS);

        Set<BasicRule> db = new HashSet<>();
        for (RelationSymbol ruleSymbol : magicProg.getRuleSymbols()) {
            db.addAll(magicProg.getRules(ruleSymbol));
        }

        UserPredicate newQ = magicProg.getQuery();
        RelationSymbol newQSymbol = newQ.getSymbol();
        Set<BasicRule> newQRules = magicProg.getRules(newQSymbol);

        // Get query q
        UserPredicate q = null;
        for (BasicRule basicRule : newQRules) {
            ComplexLiteral head = basicRule.getHead();
            UserPredicate headPred = getUserPredicate(head);
            RelationSymbol headPredSymbol = headPred.getSymbol();
            for (int i = 0; i < basicRule.getBodySize(); i++) {
                ComplexLiteral l = basicRule.getBody(i);
                q = getUserPredicate(l);
                if (q != null) {
                    break;
                }
            }
        }
        assert q != null : "Balbin evaluation method: Could not get query";

        // Get set of magic facts for q
        UserPredicate qInputAtom = MagicSetTransformer.createInputAtom(q);
        RelationSymbol qSymbol = qInputAtom.getSymbol();
        Set<BasicRule> qRules = magicProg.getRules(qSymbol);
        Set<BasicRule> qMagicFacts = null;
        UnificationPredicate magicFactMatch = UnificationPredicate.make(Var.make("true"), Var.make("true"), false);
        for (BasicRule basicRule : qRules) {
            // Determine whether basicRule is a magic fact
            UnificationPredicate unificationPredicate = null;
            for (int i = 0; i < basicRule.getBodySize(); i++) {
                unificationPredicate = getUnificationPredicate(basicRule.getBody(i));
                if (unificationPredicate.equals(magicFactMatch)) {
                    qMagicFacts.add(basicRule);
                    break;
                }
            }
        }

        // eval(qInputAtom, qMagicFacts)

        // --------------------------------------------------------------------------------
        // part 5 - setup for part 6:
        // x create a pred(p) function
        // x update the transform function in MagicSetTransformer.java
        // x create a prules(q, D) function that takes a predicate q, database D, and returns a set of rules (a subset of D)

        // part 6 - eval

        return new BalbinEvaluation(prog, magicProg.getQuery());
    }

    // TODO: Balbin, Algorithm 7 - eval
//    private static void eval(UserPredicate q, Set<BasicRule> mq) {
//
//    }

    // Balbin, Definition 29 - prules
    private static Set<BasicRule> getPRules(UserPredicate q, Set<BasicRule> db) {
        RelationSymbol qSymbol = q.getSymbol();
        Set<BasicRule> prules = new HashSet<>();

        // DefaultDirectedGraph; assuming no recursive negation
        Graph<RelationSymbol, EdgeType> g = new DefaultDirectedGraph<>(EdgeType.class);
        g.addVertex(qSymbol);

        for (BasicRule basicRule : db) {
            // Case 1 - q = pred(p0), where p0 is the head of a rule
            ComplexLiteral head = basicRule.getHead();
            UserPredicate headPred = getUserPredicate(head);
            RelationSymbol headPredSymbol = headPred.getSymbol();
            if (qSymbol.equals(headPredSymbol)) {
                prules.add(basicRule);
            }

            // Construct dependency graph g for Case 2
            g.addVertex(headPredSymbol);
            for (int i = 0; i < basicRule.getBodySize(); i++) {
                UserPredicate bodyIPred = getUserPredicate(basicRule.getBody(i));
                RelationSymbol bodyIPredSymbol = bodyIPred.getSymbol();
                g.addVertex(bodyIPredSymbol);

                EdgeType edgeType = bodyIPred.isNegated() ? EdgeType.NEGATIVE : EdgeType.POSITIVE;
                g.addEdge(bodyIPredSymbol, headPredSymbol, edgeType);
            }
        }

        // Case 2 - q <--(+) pred(p0), where p0 is the head of a rule
        AllDirectedPaths<RelationSymbol, EdgeType> allPathsG = new AllDirectedPaths<RelationSymbol, EdgeType>(g);
        List<GraphPath<RelationSymbol, EdgeType>> allPaths = null;
        for (BasicRule basicRule : db) {
            ComplexLiteral head = basicRule.getHead();
            UserPredicate headPred = getUserPredicate(head);
            RelationSymbol headPredSymbol = headPred.getSymbol();

            // Get all paths from headPredSymbol to qSymbol
            allPaths = allPathsG.getAllPaths(headPredSymbol, qSymbol, false, null);

            // Only add basicRule to prules if every edge in every path of allPaths is positive
            boolean foundNegativeEdge = false;
            for (GraphPath graphPath : allPaths) {
                List<EdgeType> edgeList = graphPath.getEdgeList();
                for (EdgeType edgeType : edgeList) {
                    if (edgeType == EdgeType.NEGATIVE) {
                        foundNegativeEdge = true;
                        break;
                    }
                }
                if (foundNegativeEdge) {
                    break;
                }
            }
            if (!foundNegativeEdge) {
                prules.add(basicRule);
            }
        }
        return prules;
    }

    private static enum EdgeType {
        NEGATIVE,
        POSITIVE
    }

    // Balbin, Definition 1 - pred(p) (for UserPredicate)
    private static UserPredicate getUserPredicate(ComplexLiteral p) {
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

    // (for UnificationPredicate)
    private static UnificationPredicate getUnificationPredicate(ComplexLiteral p) {
        return p.accept(new ComplexLiterals.ComplexLiteralVisitor<Void, UnificationPredicate>() {

            @Override
            public UnificationPredicate visit(UnificationPredicate unificationPredicate, Void input) {
                return unificationPredicate;
            }

            @Override
            public UnificationPredicate visit(UserPredicate userPredicate, Void input) {
                return null;
            }

        }, null);
    }

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
