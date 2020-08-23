package edu.harvard.seas.pl.formulog.eval;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.PushPopNaiveSolver;
import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.db.IndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.smt.*;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.unification.EmptySubstitution;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.util.*;
import edu.harvard.seas.pl.formulog.validating.FunctionDefValidation;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.*;
import org.jgrapht.Graph;
import org.jgrapht.GraphPath;
import org.jgrapht.alg.shortestpath.AllDirectedPaths;
import org.jgrapht.graph.DefaultDirectedGraph;

import java.util.*;
import java.util.function.BiFunction;

public class BalbinEvaluation implements Evaluation {

    private final SortedIndexedFactDb db;
    private final IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb;
    private final UserPredicate q;
    private final UserPredicate qInputAtom;
    private final Set<UserPredicate> qMagicFacts;
    private final Set<Term[]> qMagicFactsTerms;
    private final CountingFJP exec;
    private final Set<RelationSymbol> trackedRelations;
    private final WellTypedProgram inputProgram;
    private final Map<RelationSymbol, Set<IndexedRule>> rules;
    private final MagicSetTransformer mst;
    private final int maxPathLength;

    static final boolean sequential = System.getProperty("sequential") != null;

    @SuppressWarnings("serial")
    public static BalbinEvaluation setup(WellTypedProgram prog, int parallelism)
            throws InvalidProgramException {
        FunctionDefValidation.validate(prog);
        MagicSetTransformer mst = new MagicSetTransformer(prog);
        BasicProgram magicProg = mst.transform(false,
                MagicSetTransformer.RestoreStratification.FALSE_AND_NO_MAGIC_RULES_FOR_NEG_LITERALS);
        Set<RelationSymbol> allRelations = new HashSet<>(magicProg.getFactSymbols());
        allRelations.addAll(magicProg.getRuleSymbols());
        SortedIndexedFactDb.SortedIndexedFactDbBuilder dbb = new SortedIndexedFactDb.SortedIndexedFactDbBuilder(allRelations);
        SortedIndexedFactDb.SortedIndexedFactDbBuilder deltaDbb = new SortedIndexedFactDb.SortedIndexedFactDbBuilder(magicProg.getRuleSymbols());
        PredicateFunctionSetter predFuncs = new PredicateFunctionSetter(
                magicProg.getFunctionCallFactory().getDefManager(), dbb);

        Map<RelationSymbol, Set<IndexedRule>> rules = new HashMap<>();

        // Get query q created for magicProg by MagicSetTransformer
        UserPredicate q = magicProg.getQuery();

        // For getPRules()
        int maxPathLength = magicProg.getRuleSymbols().size() + magicProg.getFactSymbols().size() + 1;

        // Get the magic fact for q, which has body `true = true`
        Set<UserPredicate> qMagicFacts = new HashSet<>();
        UnificationPredicate magicFactMatch = UnificationPredicate.make(BoolTerm.mkTrue(), BoolTerm.mkTrue(), false);
        UserPredicate qInputAtom = null;
        for (RelationSymbol relationSymbol : magicProg.getRuleSymbols()) {
            if (relationSymbol instanceof MagicSetTransformer.InputSymbol) {
                for (BasicRule basicRule : magicProg.getRules(relationSymbol)) {
                    if (basicRule.getBody(0).equals(magicFactMatch)) {
                        qInputAtom = basicRule.getHead();
                        qMagicFacts.add(qInputAtom);
                    }
                }
            }
        }
        assert qMagicFacts != null : "Balbin evaluation: Could not get initial magic fact";

        // Normalize the args of qMagicFacts
        Set<Term[]> qMagicFactsTerms = new HashSet<>();
        try {
            qMagicFactsTerms = applySubstitution(qMagicFacts);
        } catch (EvaluationException e) {
            e.printStackTrace();
        }

        // Set up dbb and deltaDbb; add to rules
        Set<RelationSymbol> ruleSymbols = magicProg.getRuleSymbols();
        for (RelationSymbol sym : ruleSymbols) {
            Set<IndexedRule> rs = new HashSet<>();
            for (BasicRule br : magicProg.getRules(sym)) {
                for (SemiNaiveRule snr : SemiNaiveRule.make(br, ruleSymbols)) {
                    BiFunction<ComplexLiteral, Set<Var>, Integer> score = chooseScoringFunction();
                    ValidRule vr = ValidRule.make(snr, score);
                    predFuncs.preprocess(vr);
                    SimpleRule sr = SimpleRule.make(vr);
                    IndexedRule ir = IndexedRule.make(sr, p -> {
                        RelationSymbol psym = p.getSymbol();
                        if (psym instanceof SemiNaiveRule.DeltaSymbol) {
                            psym = ((SemiNaiveRule.DeltaSymbol) psym).getBaseSymbol();
                            return deltaDbb.makeIndex(psym, p.getBindingPattern());
                        } else {
                            return dbb.makeIndex(psym, p.getBindingPattern());
                        }
                    });
                    rs.add(ir);
                    if (Configuration.printFinalRules) {
                        System.err.println("[FINAL RULE]:\n" + ir);
                    }
                }
            }
            rules.put(sym, rs);
        }
        SortedIndexedFactDb db = dbb.build();
        predFuncs.setDb(db);

        SmtLibSolver smt = getSmtManager();
        try {
            smt.start(magicProg);
        } catch (EvaluationException e) {
            throw new InvalidProgramException("Problem initializing SMT shims: " + e.getMessage());
        }
        prog.getFunctionCallFactory().getDefManager().loadBuiltInFunctions(smt);

        CountingFJP exec;
        if (sequential) {
            exec = new MockCountingFJP();
        } else {
            exec = new CountingFJPImpl(parallelism);
        }

        for (RelationSymbol sym : magicProg.getFactSymbols()) {
            for (Iterable<Term[]> tups : Util.splitIterable(magicProg.getFacts(sym), Configuration.taskSize)) {
                exec.externallyAddTask(new AbstractFJPTask(exec) {

                    @Override
                    public void doTask() throws EvaluationException {
                        for (Term[] tup : tups) {
                            try {
                                db.add(sym, Terms.normalize(tup, new SimpleSubstitution()));
                            } catch (EvaluationException e) {
                                UserPredicate p = UserPredicate.make(sym, tup, false);
                                throw new EvaluationException("Cannot normalize fact " + p + ":\n" + e.getMessage());
                            }
                        }
                    }

                });
            }
        }
        exec.blockUntilFinished();
        if (exec.hasFailed()) {
            exec.shutdown();
            throw new InvalidProgramException(exec.getFailureCause());
        }
        return new BalbinEvaluation(prog, db, deltaDbb, rules, q, qInputAtom, qMagicFacts, qMagicFactsTerms, exec,
                getTrackedRelations(magicProg.getSymbolManager()), mst, maxPathLength);
    }

    private static Set<Term[]> applySubstitution(Set<UserPredicate> qMagicFacts) throws EvaluationException {
        Set<Term[]> qMagicFactsTerms = new HashSet<>();
        for (UserPredicate userPredicate : qMagicFacts) {
            Term[] args = userPredicate.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = args[i].normalize(EmptySubstitution.INSTANCE);
            }
            qMagicFactsTerms.add(newArgs);
        }
        return qMagicFactsTerms;
    }

    private static SmtLibSolver maybeDoubleCheckSolver(SmtLibSolver inner) {
        if (Configuration.smtDoubleCheckUnknowns) {
            return new DoubleCheckingSolver(inner);
        }
        return inner;
    }

    private static SmtLibSolver makeNaiveSolver() {
        return Configuration.smtUseSingleShotSolver ? new SingleShotSolver() : new CallAndResetSolver();
    }

    private static SmtLibSolver getSmtManager() {
        SmtStrategy strategy = Configuration.smtStrategy;
        switch (strategy.getTag()) {
            case QUEUE: {
                int size = (int) strategy.getMetadata();
                return new QueueSmtManager(size, () -> maybeDoubleCheckSolver(new CheckSatAssumingSolver()));
            }
            case NAIVE:
                return maybeDoubleCheckSolver(makeNaiveSolver());
            case PUSH_POP:
                return new PushPopSolver();
            case PUSH_POP_NAIVE:
                return new PushPopNaiveSolver();
            case BEST_MATCH: {
                int size = (int) strategy.getMetadata();
                return maybeDoubleCheckSolver(new BestMatchSmtManager(size));
            }
            case PER_THREAD_QUEUE: {
                int size = (int) strategy.getMetadata();
                return new PerThreadSmtManager(() -> new NotThreadSafeQueueSmtManager(size,
                        () -> maybeDoubleCheckSolver(new CheckSatAssumingSolver())));
            }
            case PER_THREAD_BEST_MATCH: {
                int size = (int) strategy.getMetadata();
                return new PerThreadSmtManager(() -> maybeDoubleCheckSolver(new BestMatchSmtManager(size)));
            }
            case PER_THREAD_PUSH_POP: {
                return new PerThreadSmtManager(() -> new PushPopSolver());
            }
            case PER_THREAD_PUSH_POP_NAIVE: {
                return new PerThreadSmtManager(() -> new PushPopNaiveSolver());
            }
            case PER_THREAD_NAIVE: {
                return new PerThreadSmtManager(() -> maybeDoubleCheckSolver(
                        Configuration.smtUseSingleShotSolver ? new SingleShotSolver() : new CallAndResetSolver()));
            }
            default:
                throw new UnsupportedOperationException("Cannot support SMT strategy: " + strategy);
        }
    }

    static Set<RelationSymbol> getTrackedRelations(SymbolManager sm) {
        Set<RelationSymbol> s = new HashSet<>();
        for (String name : Configuration.trackedRelations) {
            if (sm.hasName(name)) {
                Symbol sym = sm.lookupSymbol(name);
                if (sym instanceof RelationSymbol) {
                    s.add((RelationSymbol) sm.lookupSymbol(name));
                } else {
                    System.err.println("[WARNING] Cannot track non-relation " + sym);
                }

            } else {
                System.err.println("[WARNING] Cannot track unrecognized relation " + name);
            }
        }
        return s;
    }

    static BiFunction<ComplexLiteral, Set<Var>, Integer> chooseScoringFunction() {
        return BalbinEvaluation::score0;
    }

    static int score0(ComplexLiteral l, Set<Var> boundVars) {
        return 0;
    }

    BalbinEvaluation(WellTypedProgram inputProgram, SortedIndexedFactDb db,
                     IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb, Map<RelationSymbol, Set<IndexedRule>> rules,
                     UserPredicate q, UserPredicate qInputAtom, Set<UserPredicate> qMagicFacts,
                     Set<Term[]> qMagicFactsTerms, CountingFJP exec, Set<RelationSymbol> trackedRelations,
                     MagicSetTransformer mst, int maxPathLength) {
        this.inputProgram = inputProgram;
        this.db = db;
        this.q = q;
        this.qInputAtom = qInputAtom;
        this.qMagicFacts = qMagicFacts;
        this.qMagicFactsTerms = qMagicFactsTerms;
        this.exec = exec;
        this.trackedRelations = trackedRelations;
        this.deltaDbb = deltaDbb;
        this.rules = rules;
        this.mst = mst;
        this.maxPathLength = maxPathLength;
    }

    @Override
    public WellTypedProgram getInputProgram() {
        return inputProgram;
    }

    @Override
    public synchronized void run() throws EvaluationException {
        if (Configuration.printRelSizes) {
            Runtime.getRuntime().addShutdownHook(new Thread() {

                @Override
                public void run() {
                    Configuration.printRelSizes(System.err, "REL SIZE", db, true);
                }

            });
        }
        if (Configuration.debugParallelism) {
            Runtime.getRuntime().addShutdownHook(new Thread() {

                @Override
                public void run() {
                    System.err.println("[STEAL COUNT] " + exec.getStealCount());
                }

            });
        }
        eval();
    }

    // Balbin, Algorithm 7 - eval
    private void eval() throws EvaluationException {
        List<IndexedRule> pRules = new ArrayList<>();
        pRules.addAll(getPRules(qInputAtom, rules, maxPathLength));
        System.out.println("pRules:");
        System.out.println(pRules);

        // Create new BalbinEvaluationContext
        MagicSetTransformer.InputSymbol qInputSymbol = (MagicSetTransformer.InputSymbol) qInputAtom.getSymbol();
        new BalbinEvaluationContext(db, deltaDbb, qInputSymbol.getBaseSymbol(), qMagicFactsTerms, pRules, rules, exec, trackedRelations, mst, maxPathLength)
                .evaluate();
    }

    // - prules (with IndexedRule)
    public static Set<IndexedRule> getPRules(UserPredicate q, Map<RelationSymbol, Set<IndexedRule>> rules, int maxPathLength) {
        System.out.print("q: ");
        System.out.println(q);
        Set<IndexedRule> db = new HashSet<>();
        for (Map.Entry<RelationSymbol, Set<IndexedRule>> entry : rules.entrySet()) {
            db.addAll(entry.getValue());
        }

        RelationSymbol qSymbol = q.getSymbol();
        Set<IndexedRule> prules = new HashSet<>();

        // DefaultDirectedGraph; assuming no recursive negation
        Graph<RelationSymbol, DependencyTypeWrapper> g = new DefaultDirectedGraph<>(DependencyTypeWrapper.class);
        g.addVertex(qSymbol);

        for (IndexedRule indexedRule : db) {
            // Case 1 - q = pred(p0), where p0 is the head of a rule
            SimplePredicate headPred = indexedRule.getHead();
            RelationSymbol headPredSymbol = headPred.getSymbol();
            if (qSymbol.equals(headPredSymbol)) {
                prules.add(indexedRule);
//                System.out.print("case 1 - add rule: ");
//                System.out.println(indexedRule);
            }

            // Construct dependency graph g for Case 2
            g.addVertex(headPredSymbol);
            System.out.print("symbol " + headPredSymbol + " in g: ");
            System.out.println(g.containsVertex(headPredSymbol));
            for (int i = 0; i < indexedRule.getBodySize(); i++) {
                // Not going to work for ML functions that refer to predicates
                SimplePredicate bodyIPred = getSimplePredicate(indexedRule.getBody(i));
                if (bodyIPred != null) {
                    RelationSymbol bodyIPredSymbol = bodyIPred.getSymbol();
                    g.addVertex(bodyIPredSymbol);

//                    System.out.print("bodyIPred: ");
//                    System.out.print(bodyIPred + ", ");
//                    System.out.println(bodyIPred.isNegated());
                    EdgeType edgeType = bodyIPred.isNegated() ? EdgeType.NEGATIVE : EdgeType.POSITIVE;
                    g.addEdge(bodyIPredSymbol, headPredSymbol, new DependencyTypeWrapper(edgeType));
                }
            }
        }

        // Case 2 - q <--(+) pred(p0), where p0 is the head of a rule
        AllDirectedPaths<RelationSymbol, DependencyTypeWrapper> allPathsG = new AllDirectedPaths<>(g);
        System.out.print("allPathsG: ");
        System.out.println(allPathsG);
        List<GraphPath<RelationSymbol, DependencyTypeWrapper>> allPaths = null;
        for (IndexedRule indexedRule : db) {
            SimplePredicate headPred = indexedRule.getHead();
            RelationSymbol headPredSymbol = headPred.getSymbol();

            // Get all paths from headPredSymbol to qSymbol
            // Todo: Check that getAllPaths is working as expected (i.e. for cycles)
            // Todo (error): getAllPaths is returning empty; it's possible that headPredSymbol is represented differently
            //  when that symbol is in the body of a rule. See line 379 where edges are being added.
            allPaths = allPathsG.getAllPaths(headPredSymbol, qSymbol, false, maxPathLength);
            System.out.print("allPaths: ");
            System.out.println(allPaths);

            // Only add basicRule to prules if every edge in every path of allPaths is positive
            boolean foundNegativeEdge = false;
            for (GraphPath graphPath : allPaths) {
                List<DependencyTypeWrapper> edgeList = graphPath.getEdgeList();
                System.out.print("edgeList: ");
                System.out.println(edgeList);
                for (DependencyTypeWrapper e : edgeList) {
                    EdgeType edgeType = e.get();
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
                prules.add(indexedRule);
//                System.out.print("case 2 - add rule: ");
//                System.out.println(indexedRule);
            }
        }
        return prules;
    }

    private static enum EdgeType {
        NEGATIVE,
        POSITIVE
    }

    // Needed because edges need to have unique objects as labels...
    private static class DependencyTypeWrapper {

        private final EdgeType e;

        public DependencyTypeWrapper(EdgeType e) {
            this.e = e;
        }

        public EdgeType get() {
            return e;
        }

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

    // - pred(p) (for UnificationPredicate)
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

    // - pred(p) (for SimplePredicate)
    private static SimplePredicate getSimplePredicate(SimpleLiteral p) {
        return p.accept(new SimpleLiteralVisitor<Void, SimplePredicate>() {

            @Override
            public SimplePredicate visit(Assignment assignment, Void input) {
                return null;
            }

            @Override
            public SimplePredicate visit(Check check, Void input) {
                return null;
            }

            @Override
            public SimplePredicate visit(Destructor destructor, Void input) {
                return null;
            }

            @Override
            public SimplePredicate visit(SimplePredicate simplePredicate, Void input) {
                return simplePredicate;
            }

        }, null);
    }

    public Set<IndexedRule> getRules(RelationSymbol sym) {
        return Collections.unmodifiableSet(rules.get(sym));
    }

    @Override
    public synchronized EvaluationResult getResult() {
        return new EvaluationResult() {

            @Override
            public Iterable<UserPredicate> getAll(RelationSymbol sym) {
                if (!db.getSymbols().contains(sym)) {
                    throw new IllegalArgumentException("Unrecognized relation symbol " + sym);
                }
                return new Iterable<UserPredicate>() {

                    @Override
                    public Iterator<UserPredicate> iterator() {
                        return new FactIterator(sym, db.getAll(sym).iterator());
                    }

                };
            }

            @Override
            public Iterable<UserPredicate> getQueryAnswer() {
                if (q == null) {
                    return null;
                }
                RelationSymbol querySym = q.getSymbol();
                return new Iterable<UserPredicate>() {

                    @Override
                    public Iterator<UserPredicate> iterator() {
                        return new FactIterator(querySym, db.getAll(querySym).iterator());
                    }

                };
            }

            @Override
            public Set<RelationSymbol> getSymbols() {
                return Collections.unmodifiableSet(db.getSymbols());
            }

        };
    }

    static class FactIterator implements Iterator<UserPredicate> {

        final RelationSymbol sym;
        final Iterator<Term[]> bindings;

        public FactIterator(RelationSymbol sym, Iterator<Term[]> bindings) {
            this.sym = sym;
            this.bindings = bindings;
        }

        @Override
        public boolean hasNext() {
            return bindings.hasNext();
        }

        @Override
        public UserPredicate next() {
            return UserPredicate.make(sym, bindings.next(), false);
        }

    }

    @Override
    public boolean hasQuery() {
        return q != null;
    }

    @Override
    public UserPredicate getQuery() {
        return q;
    }

    public SortedIndexedFactDb getDb() {
        return db;
    }

    public IndexedFactDbBuilder<SortedIndexedFactDb> getDeltaDbb() {
        return deltaDbb;
    }

}
