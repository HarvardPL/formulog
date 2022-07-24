package edu.harvard.seas.pl.formulog.codegen;

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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Triple;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

/**
 * This class is used to produce C++ code corresponding to the evaluation of a
 * literal in a Formulog rule.
 */
public class LiteralCodeGen {

    private final CodeGenContext ctx;

    public LiteralCodeGen(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    /**
     * We should use "hints" when querying and manipulating the data structures for
     * these relations. This improves the performance of Souffle's B-trees.
     */
    private final Set<Relation> hints = new HashSet<>();
    private boolean hintsEnabled;

    /**
     * Set which relations should be treated with "hints" if hints are enabled.
     * Hints make data structure accesses faster. Hints are not actually used until
     * after the {@link #enableHints() enableHints()} method is called.
     *
     * @param the relations which should be accessed with hints
     */
    public void setHints(Set<Relation> hints) {
        this.hints.clear();
        this.hints.addAll(hints);
    }

    /**
     * Enable the use of hints.
     */
    public void enableHints() {
        hintsEnabled = true;
    }

    /**
     * Generate the code for evaluating a predicate lookup.
     *
     * @param pred        The predicate
     * @param index       Database index to use for lookup
     * @param parallelize Whether to parallelize evaluation, if applicable
     * @param env         The current environment
     * @return The generated C++ code and related metadata
     */
    public Result gen(SimplePredicate pred, int index, boolean parallelize, Map<Var, CppExpr> env) {
        return gen1(pred, index, parallelize, env);
    }

    /**
     * Generate the code for evaluating an assignment literal.
     *
     * @param assn The literal
     * @param env  The current environment
     * @return The generated C++ code and related metadata
     */
    public Result gen(Assignment assn, Map<Var, CppExpr> env) {
        return gen1(assn, -1, false, env);
    }

    /**
     * Generate the code for evaluating a destructor literal.
     *
     * @param dtor The literal
     * @param env  The current environment
     * @return The generated C++ code and related metadata
     */
    public Result gen(Destructor dtor, Map<Var, CppExpr> env) {
        return gen1(dtor, -1, false, env);
    }

    /**
     * Generate the code for evaluating a check literal.
     *
     * @param check The literal
     * @param env   The current environment
     * @return The generated C++ code and related metadata
     */
    public Result gen(Check check, Map<Var, CppExpr> env) {
        return gen1(check, -1, false, env);
    }

    private Result gen1(SimpleLiteral l, int index, boolean parallelize, Map<Var, CppExpr> env) {
        return new Worker(index, parallelize, new HashMap<>(env)).go(l);
    }

    private class Worker {

        private final Map<Var, CppExpr> env;
        private final TermCodeGen tcg = new TermCodeGen(ctx);
        /**
         * Database index to use, if doing a lookup.
         */
        private final int index;
        /**
         * Whether to parallelize evaluation, if applicable.
         */
        private final boolean parallelize;

        public Worker(int index, boolean parallelize, Map<Var, CppExpr> env) {
            this.index = index;
            this.env = env;
            this.parallelize = parallelize;
        }

        public Result go(SimpleLiteral l) {
            Pair<Function<CppStmt, CppStmt>, CodeShape> p = l.accept(visitor, null);
            return new Result(p.fst(), env, p.snd());
        }

        private final SimpleLiteralVisitor<Void, Pair<Function<CppStmt, CppStmt>, CodeShape>> visitor = new SimpleLiteralVisitor<Void, Pair<Function<CppStmt, CppStmt>, CodeShape>>() {

            @Override
            public Pair<Function<CppStmt, CppStmt>, CodeShape> visit(Assignment assignment, Void input) {
                return new Pair<>(handleAssignment(assignment), CodeShape.OTHER);
            }

            @Override
            public Pair<Function<CppStmt, CppStmt>, CodeShape> visit(Check check, Void input) {
                return new Pair<>(handleCheck(check), CodeShape.OTHER);
            }

            @Override
            public Pair<Function<CppStmt, CppStmt>, CodeShape> visit(Destructor destructor, Void input) {
                return new Pair<>(handleDestructor(destructor), CodeShape.OTHER);
            }

            @Override
            public Pair<Function<CppStmt, CppStmt>, CodeShape> visit(SimplePredicate predicate, Void input) {
                if (predicate.isNegated()) {
                    return new Pair<>(handleNegativePred(predicate), CodeShape.LOOKUP);
                } else {
                    return handlePositivePred(predicate);
                }
            }

        };

        /**
         * Generate code encoding an assignment, i.e., assigning an expression to a
         * variable.
         *
         * @param assignment The assignment literal
         * @return A continuation encoding the literal's evaluation
         */
        private Function<CppStmt, CppStmt> handleAssignment(Assignment assignment) {
            Var x = assignment.getDef();
            Term val = assignment.getVal();
            Pair<CppStmt, CppExpr> p = tcg.gen(val, env);
            String id = ctx.newId("x");
            CppStmt def = CppDecl.mk(id, p.snd());
            CppVar var = CppVar.mk(id);
            env.put(x, var);
            return s -> CppSeq.mk(p.fst(), def, s);
        }

        /**
         * Generate code encoding a check literal, i.e., whether two expressions
         * evaluate to the same thing.
         *
         * @param check The check literal
         * @return A continuation encoding the literal's evaluation
         */
        private Function<CppStmt, CppStmt> handleCheck(Check check) {
            Term lhs = check.getLhs();
            Term rhs = check.getRhs();
            Pair<CppStmt, CppExpr> p1 = tcg.gen(lhs, env);
            Pair<CppStmt, CppExpr> p2 = tcg.gen(rhs, env);
            CppExpr term1 = p1.snd();
            CppExpr term2 = p2.snd();
            CppExpr guard = CppFuncCall.mk("Term::compare", term1, term2);
            if (!check.isNegated()) {
                guard = CppUnop.mkNot(guard);
            }
            final CppExpr guard2 = guard;
            return s -> CppSeq.mk(p1.fst(), p2.fst(), CppIf.mk(guard2, s));
        }

        /**
         * Generate code encoding a destructor literal, i.e., extracting the components
         * of a complex term.
         *
         * @param destructor The destructor literal
         * @return A continuation encoding the literal's evaluation
         */
        private Function<CppStmt, CppStmt> handleDestructor(Destructor destructor) {
            Pair<CppStmt, CppExpr> p = tcg.gen(destructor.getScrutinee(), env);
            CppExpr base = p.snd();
            CppVar sym = CppVar.mk(ctx.lookupRepr(destructor.getSymbol()));
            CppExpr guard = CppBinop.mkEq(CppAccess.mkThruPtr(base, "sym"), sym);
            List<CppStmt> stmts = new ArrayList<>();
            int i = 0;
            for (Var x : destructor.getBindings()) {
                String id = ctx.newId("x");
                stmts.add(CppDecl.mk(id, CodeGenUtil.mkComplexTermLookup(base, i)));
                env.put(x, CppVar.mk(id));
                i++;
            }
            CppStmt assignments = CppSeq.mk(stmts);
            return s -> CppSeq.mk(p.fst(), CppIf.mk(guard, CppSeq.mk(assignments, s)));
        }

        /**
         * Generate code for evaluating a negated predicate.
         *
         * @param pred The negated predicate
         * @return A continuation encoding the predicate's evaluation
         */
        private Function<CppStmt, CppStmt> handleNegativePred(SimplePredicate pred) {
            return mkContains(pred);
        }

        /**
         * Generate code for evaluating a positive (i.e., non-negated) predicate.
         *
         * @param pred The positive predicate
         * @return A continuation encoding the predicate's evaluation
         */
        private Pair<Function<CppStmt, CppStmt>, CodeShape> handlePositivePred(SimplePredicate pred) {
            if (!hasFreeArgs(pred)) {
                return new Pair<>(mkContains(pred), CodeShape.LOOKUP);
            } else {
                Triple<Function<CppStmt, CppStmt>, CppExpr, CodeShape> tri = genTupleIterator(pred);
                Function<CppStmt, CppStmt> loop = genLoop(pred, tri.second);
                return new Pair<>(s -> tri.first.apply(loop.apply(s)), tri.third);
            }
        }

        /**
         * Return true if the given relation should be accessed with database hints.
         *
         * @param rel The relation
         * @return Whether to use a hint
         */
        private boolean useHint(Relation rel) {
            return hintsEnabled && hints.contains(rel);
        }

        /**
         * Generate a C++ if statement that checks whether a predicate holds. The
         * arguments to the predicate cannot contain unbound variables.
         *
         * @param pred The predicate that is being encoded
         * @return A continuation that expects the body of the if statement
         */
        private Function<CppStmt, CppStmt> mkContains(SimplePredicate pred) {
            Pair<CppStmt, CppExpr> key = genKey(pred);
            Relation rel = ctx.lookupRelation(pred.getSymbol());
            CppExpr guard = rel.mkContains(index, key.snd(), useHint(rel));
            if (pred.isNegated()) {
                guard = CppUnop.mkNot(guard);
            }
            final CppExpr guard2 = guard;
            return s -> CppSeq.mk(key.fst(), CppIf.mk(guard2, s));
        }

        /**
         * Return whether the predicate has some arguments with unbound variables.
         *
         * @param pred The predicate
         * @return Whether the predicate has arguments with unbound variables
         */
        private boolean hasFreeArgs(SimplePredicate pred) {
            for (BindingType ty : pred.getBindingPattern()) {
                if (ty == BindingType.FREE) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Generate a C++ loop over all the tuples that satisfy the given predicate.
         *
         * @param pred The predicate
         * @return A triple consisting of a continuation expecting the body of the loop,
         * an expression for the tuple iterator itself, and a marker of the
         * "shape" of the loop (i.e., whether it is parallel or not).
         */
        private Triple<Function<CppStmt, CppStmt>, CppExpr, CodeShape> genTupleIterator(SimplePredicate pred) {
            if (parallelize) {
                Pair<Function<CppStmt, CppStmt>, CppExpr> p = genParallelLoop(pred);
                return new Triple<>(p.fst(), p.snd(), CodeShape.PARALLEL_LOOP);
            } else {
                Pair<Function<CppStmt, CppStmt>, CppExpr> p = genNormalLookup(pred);
                return new Triple<>(p.fst(), p.snd(), CodeShape.LOOP);
            }
        }

        /**
         * Generate a parallelized C++ loop over the partitions of the relation
         * specified by the given predicate.
         *
         * @param pred The predicate
         * @return A pair of a continuation expecting the loop body and the partition
         * iterator itself
         */
        private Pair<Function<CppStmt, CppStmt>, CppExpr> genParallelLoop(SimplePredicate pred) {
            Pair<Function<CppStmt, CppStmt>, String> p = genPartition(pred);
            String part = p.snd();
            CppVar it = CppVar.mk("it");
            // The for loop needs to follow a particular form to be picked up by OpenMP
            CppExpr init = CppExprFromString.mk(part + ".begin()");
            CppExpr guard = CppExprFromString.mk("it < " + part + ".end()");
            CppExpr update = CppExprFromString.mk("++it");
            CppStmt decls = mkContextDeclarations();
            Function<CppStmt, CppStmt> forLoop = body -> CppSeq.mk(CppVar.mk("PARALLEL_START").toStmt(), decls,
                    CppFor.mkParallel("it", init, guard, update, body), CppVar.mk("PARALLEL_END").toStmt());
            return new Pair<>(body -> p.fst().apply(forLoop.apply(body)), CppUnop.mkDeref(it));
        }

        /**
         * Generate code declaring the relation contexts used for hints.
         *
         * @return the declaration code
         */
        private CppStmt mkContextDeclarations() {
            List<CppStmt> stmts = new ArrayList<>();
            for (Relation rel : hints) {
                stmts.add(rel.mkDeclContext());
            }
            return CppSeq.mk(stmts);
        }

        /**
         * Generate code partitioning a relation into chunks that can be evaluated in
         * parallel.
         *
         * @param pred The predicate corresponding to the relation that is being looped
         *             over
         * @return A pair consisting of a continuation expecting the code that follows
         * the partition, and the name of the partition iterator itself
         */
        private Pair<Function<CppStmt, CppStmt>, String> genPartition(SimplePredicate pred) {
            if (!containsBoundPosition(pred.getBindingPattern())) {
                CppStmt assign = CppDecl.mk("part", lookupRelation(pred).mkPartition());
                return new Pair<>(s -> CppSeq.mk(assign, s), "part");
            } else {
                Pair<Function<CppStmt, CppStmt>, CppExpr> p = genNormalLookup(pred);
                CppStmt assign = CppDecl.mk("part", CppMethodCall.mk(p.snd(), "partition"));
                return new Pair<>(s -> p.fst().apply(CppSeq.mk(assign, s)), "part");
            }
        }

        /**
         * Returns true iff at least one member in an array of binding types represents
         * a bound position.
         *
         * @param pat The binding types
         * @return True iff at least one member in the input array represents a bound
         * position
         */
        private boolean containsBoundPosition(BindingType[] pat) {
            for (BindingType binding : pat) {
                if (binding == BindingType.BOUND) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Generate the "key" that is used when indexing into a relation.
         *
         * @param pred The predicate that corresponds to the lookup
         * @return A pair of the code generating the key and an expression for the key
         * itself
         */
        private Pair<CppStmt, CppExpr> genKey(SimplePredicate pred) {
            List<CppStmt> stmts = new ArrayList<>();
            String tupName = ctx.newId("key");
            CppVar tup = CppVar.mk(tupName);
            Relation rel = ctx.lookupRelation(pred.getSymbol());
            stmts.add(rel.mkDeclTuple(tupName));
            Term[] args = pred.getArgs();
            int i = 0;
            for (BindingType ty : pred.getBindingPattern()) {
                if (ty == BindingType.BOUND) {
                    Pair<CppStmt, CppExpr> p = tcg.gen(args[i], env);
                    stmts.add(p.fst());
                    CppExpr idx = CppConst.mkInt(i);
                    stmts.add(CppBinop.mkAssign(CppSubscript.mk(tup, idx), p.snd()).toStmt());
                }
                i++;
            }
            return new Pair<>(CppSeq.mk(stmts), tup);
        }

        /**
         * Generate a relation lookup.
         *
         * @param pred The predicate that corresponds to the lookup
         * @return A pair of a continuation expecting the code following the lookup and
         * a tuple iterator (for accessing the result of the lookup)
         */
        private Pair<Function<CppStmt, CppStmt>, CppExpr> genNormalLookup(SimplePredicate pred) {
            Pair<CppStmt, CppExpr> p = genKey(pred);
            Relation rel = ctx.lookupRelation(pred.getSymbol());
            CppExpr call = rel.mkLookup(index, pred.getBindingPattern(), p.snd(), useHint(rel));
            return new Pair<>(s -> CppSeq.mk(p.fst(), s), call);
        }

        /**
         * Generate a sequential loop over the tuples that satisfy the given predicate.
         *
         * @param pred The predicate
         * @param it   The tuple iterator to loop over
         * @return a continuation expecting the loop body
         */
        private Function<CppStmt, CppStmt> genLoop(SimplePredicate pred, CppExpr it) {
            Relation rel = lookupRelation(pred);
            String tup = ctx.newId("tup");
            List<CppStmt> assignments = new ArrayList<>();
            BindingType[] pat = pred.getBindingPattern();
            int i = 0;
            for (Term t : pred.getArgs()) {
                if (pat[i] == BindingType.FREE) {
                    String id = ctx.newId("x");
                    CppExpr access = rel.mkTupleAccess(CppVar.mk(tup), CppConst.mkInt(i));
                    assignments.add(CppDecl.mk(id, access));
                    env.put((Var) t, CppVar.mk(id));
                }
                i++;
            }
            CppStmt all = CppSeq.mk(assignments);
            return s -> CppForEach.mk(tup, it, CppSeq.mk(all, s));
        }

        /**
         * Get the relation that corresponds to the given predicate.
         *
         * @param pred The predicate
         * @return The relation
         */
        private Relation lookupRelation(SimplePredicate pred) {
            return ctx.lookupRelation(pred.getSymbol());
        }

    }

    /**
     * This enum encodes the kind of C++ code generated for evaluating a literal.
     */
    public static enum CodeShape {
        LOOKUP, LOOP, PARALLEL_LOOP, OTHER;
    }

    /**
     * This class represents the result of generating C++ code for a Formulog rule
     * literal.
     */
    public static class Result {

        private final Function<CppStmt, CppStmt> k;
        private final Map<Var, CppExpr> newEnv;
        private final CodeShape resType;

        private Result(Function<CppStmt, CppStmt> k, Map<Var, CppExpr> newEnv, CodeShape resType) {
            this.k = k;
            this.newEnv = newEnv;
            this.resType = resType;
        }

        /**
         * Get a continuation that represents the generated C++ code for a literal. It
         * should be applied to the C++ code for evaluating the rest of the rule.
         *
         * @return The continuation
         */
        public Function<CppStmt, CppStmt> getK() {
            return k;
        }

        /**
         * Get an updated environment that includes bindings for variables that are
         * assigned while evaluating the literal.
         *
         * @return The new environment
         */
        public Map<Var, CppExpr> getNewEnv() {
            return newEnv;
        }

        /**
         * Find out what kind of C++ code was generated for evaluating this literal.
         *
         * @return The shape of the C++ code
         */
        public CodeShape getCodeShape() {
            return resType;
        }

    }

}
