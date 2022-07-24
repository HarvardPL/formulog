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
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.codegen.ast.cpp.*;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

/**
 * This class is used to take a Formulog term and generate its C++
 * representation.
 */
public class TermCodeGen {

    private final CodeGenContext ctx;

    public TermCodeGen(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    public CppExpr mkBool(CppExpr bool) {
        return CppFuncCall.mk("Term::make<bool>", bool);
    }

    /*
     * EZ: mkComplex no longer requires supporting statements, but these methods
     * still exist in order to not break the rest of the code.
     *
     * AB: Probably makes sense to keep the current signature - I don't think it
     * causes any significant harm, and it gives us some future flexibility.
     */

    /**
     * Generate the C++ representation of a complex term given the symbol of a
     * constructor and its arguments.
     *
     * @param sym
     * @param args
     * @return A pair of a C++ statement and a C++ expression representing the
     * complex term; the statement should be executed before the expression
     * is used.
     */
    public Pair<CppStmt, CppExpr> mkComplex(ConstructorSymbol sym, List<CppExpr> args) {
        assert sym.getArity() == args.size();
        CppVar symbol = CppVar.mk(ctx.lookupRepr(sym));
        CppExpr val = CppFuncCall.mk("Term::make<" + symbol + ">", args);
        return new Pair<>(CppSeq.mk(), val);
    }

    /**
     * Generate the C++ representation of a complex term given the symbol of a
     * constructor and its arguments.
     *
     * @param sym
     * @param args
     * @return A pair of a C++ statement and a C++ expression representing the
     * complex term; the statement should be executed before the expression
     * is used.
     */
    public Pair<CppStmt, CppExpr> mkComplex(ConstructorSymbol sym, CppExpr... args) {
        return mkComplex(sym, Arrays.asList(args));
    }

    /**
     * Generate the C++ representation of a complex term given the symbol of a
     * constructor and its arguments.
     *
     * @param acc  An accumulator list of statements; these should be executed before
     *             the returned expression is used
     * @param sym
     * @param args
     * @return A C++ expression representing the complex term
     */
    public CppExpr mkComplex(List<CppStmt> acc, ConstructorSymbol sym, CppExpr... args) {
        Pair<CppStmt, CppExpr> p = mkComplex(sym, args);
        acc.add(p.fst());
        return p.snd();
    }

    /**
     * Generate the C++ representation of a complex term given the symbol of a
     * constructor and its arguments.
     *
     * @param acc  An accumulator list of statements; these should be executed before
     *             the returned expression is used
     * @param sym
     * @param args
     * @return A C++ expression representing the complex term
     */
    public CppExpr mkComplex(List<CppStmt> acc, ConstructorSymbol sym, List<CppExpr> args) {
        Pair<CppStmt, CppExpr> p = mkComplex(sym, args);
        acc.add(p.fst());
        return p.snd();
    }

    /**
     * Generate the C++ representation of a term, given an environment mapping
     * Formulog variables to C++ expressions.
     *
     * @param t
     * @param env
     * @return A pair of a C++ statement and a C++ expression representing the term;
     * the statement should be executed before the expression is used.
     */
    public Pair<CppStmt, CppExpr> gen(Term t, Map<Var, CppExpr> env) {
        List<CppStmt> acc = new ArrayList<>();
        CppExpr e = gen(acc, t, env);
        return new Pair<>(CppSeq.mk(acc), e);
    }

    /**
     * Generate the C++ representation of a term, given an environement mapping
     * Formulog variables to C++ expressions.
     *
     * @param acc  An accumulator list of statements; these should be executed before
     *             the returned expression is used
     * @param sym
     * @param args
     * @return A C++ expression representing the term
     */
    public CppExpr gen(List<CppStmt> acc, Term t, Map<Var, CppExpr> env) {
        return new Worker(acc, env).go(t);
    }

    /**
     * Generate the C++ representation of a term, given an environement mapping
     * Formulog variables to C++ expressions.
     *
     * @param acc  An accumulator list of statements; these should be executed before
     *             the returned expression is used
     * @param sym
     * @param args
     * @return C++ expressions representing the terms (in order)
     */
    public List<CppExpr> gen(List<CppStmt> acc, List<Term> ts, Map<Var, CppExpr> env) {
        List<CppExpr> exprs = new ArrayList<>();
        for (Term t : ts) {
            exprs.add(gen(acc, t, env));
        }
        return exprs;
    }

    /**
     * Generate the C++ representation of some terms, given an environment mapping
     * Formulog variables to C++ expressions.
     *
     * @param ts
     * @param env
     * @return A pair of a C++ statement and a list of C++ expressions representing
     * the terms (in order); the statement should be executed before the
     * expressions are used.
     */
    public Pair<CppStmt, List<CppExpr>> gen(List<Term> ts, Map<Var, CppExpr> env) {
        List<CppStmt> acc = new ArrayList<>();
        List<CppExpr> es = gen(acc, ts, env);
        return new Pair<>(CppSeq.mk(acc), es);
    }

    private class Worker {

        private final Map<Var, CppExpr> env;
        private final List<CppStmt> acc;
        private final MatchCodeGen mcg = new MatchCodeGen(ctx);

        public Worker(List<CppStmt> acc, Map<Var, CppExpr> env) {
            this.acc = acc;
            this.env = env;
        }

        public CppExpr go(Term t) {
            return t.accept(tv, null);
        }

        private final TermVisitor<Void, CppExpr> tv = new TermVisitor<Void, CppExpr>() {

            @Override
            public CppExpr visit(Var x, Void in) {
                assert env.containsKey(x);
                return env.get(x);
            }

            @Override
            public CppExpr visit(Constructor c, Void in) {
                ConstructorSymbol sym = c.getSymbol();
                Term[] args = c.getArgs();
                List<CppExpr> cppArgs = new ArrayList<>();
                for (Term arg : args) {
                    cppArgs.add(arg.accept(this, in));
                }
                CppExpr term = mkComplex(acc, sym, cppArgs);
                String tId = ctx.newId("t");
                acc.add(CppDecl.mk(tId, term));
                return CppVar.mk(tId);
            }

            @Override
            public CppExpr visit(Primitive<?> p, Void in) {
                return CppBaseTerm.mk(p);
            }

            @Override
            public CppExpr visit(Expr e, Void in) {
                return e.accept(ev, in);
            }

        };

        private final ExprVisitor<Void, CppExpr> ev = new ExprVisitor<Void, CppExpr>() {

            @Override
            public CppExpr visit(MatchExpr matchExpr, Void in) {
                Pair<CppStmt, CppExpr> p = mcg.gen(matchExpr, env);
                acc.add(p.fst());
                return p.snd();
            }

            @Override
            public CppExpr visit(FunctionCall funcCall, Void in) {
                List<CppExpr> args = new ArrayList<>();
                for (Term arg : funcCall.getArgs()) {
                    args.add(arg.accept(tv, in));
                }
                return CppFuncCall.mk(ctx.lookupRepr(funcCall.getSymbol()), args);
            }

            @Override
            public CppExpr visit(LetFunExpr funcDefs, Void in) {
                throw new AssertionError("impossible");
            }

            @Override
            public CppExpr visit(Fold fold, Void in) {
                throw new UnsupportedOperationException("Not supporting codegen for fold");
            }

        };

    }

}
