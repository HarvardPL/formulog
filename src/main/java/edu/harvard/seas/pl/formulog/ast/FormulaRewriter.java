package edu.harvard.seas.pl.formulog.ast;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2021 President and Fellows of Harvard College
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

import java.util.*;

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamKind;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public class FormulaRewriter {

    private final FunctionCallFactory funcFactory;
    private final Map<Var, Types.Type> env;
    private boolean inFormula;

    public FormulaRewriter(FunctionCallFactory funcFactory, Map<Var, Types.Type> env) {
        this.funcFactory = funcFactory;
        this.env = env;
    }

    public Term rewrite(Term t) {
        return rewrite(t, false, false);
    }

    public Term rewrite(Term t, boolean inPattern) {
        return rewrite(t, inPattern, false);
    }

    public Term rewrite(Term t, boolean inPattern, boolean inFormula) {
        this.inFormula = inFormula;
        return t.accept(termRewriter, inPattern);
    }

    private final TermVisitor<Boolean, Term> termRewriter = new TermVisitor<Boolean, Term>() {

        private Term handleBuiltInConstructor(Constructor ctor, boolean inPattern) {
            BuiltInConstructorSymbol sym = (BuiltInConstructorSymbol) ctor.getSymbol();
            Term[] args = ctor.getArgs();
            Term[] newArgs = new Term[args.length];
            switch (sym) {
                case ENTER_FORMULA: {
                    boolean wasInFormula = inFormula;
                    inFormula = true;
                    Term t = args[0].accept(this, inPattern);
                    inFormula = wasInFormula;
                    return t;
                }
                case EXIT_FORMULA: {
                    boolean wasInFormula = inFormula;
                    inFormula = false;
                    Term arg = args[0].accept(this, inPattern);
                    inFormula = wasInFormula;
                    return arg;
                }
                case INT_CONST:
                case INT_BIG_CONST: {
                    assert args.length == 1;
                    boolean wasInFormula = inFormula;
                    inFormula = false;
                    newArgs[0] = args[0].accept(this, inPattern);
                    inFormula = wasInFormula;
                }
                break;
                default:
                    for (int i = 0; i < args.length; ++i) {
                        newArgs[i] = args[i].accept(this, inPattern);
                    }
            }
            return ctor.copyWithNewArgs(newArgs);
        }

        private Term handleParameterizedConstructor(Constructor ctor, boolean inPattern) {
            ParameterizedConstructorSymbol sym = (ParameterizedConstructorSymbol) ctor.getSymbol();
            Term[] args = ctor.getArgs();
            Term[] newArgs = new Term[args.length];
            switch (sym.getBase()) {
                case BV_CONST:
                case BV_BIG_CONST:
                case FP_CONST:
                case FP_BIG_CONST: {
                    assert args.length == 1;
                    boolean wasInFormula = inFormula;
                    inFormula = false;
                    newArgs[0] = args[0].accept(this, inPattern);
                    inFormula = wasInFormula;
                }
                break;
                case BV_EXTRACT: {
                    assert args.length == 3;
                    newArgs[0] = args[0].accept(this, inPattern);
                    boolean wasInFormula = inFormula;
                    inFormula = false;
                    newArgs[1] = args[1].accept(this, inPattern);
                    newArgs[2] = args[2].accept(this, inPattern);
                    inFormula = wasInFormula;
                }
                break;
                default:
                    for (int i = 0; i < args.length; ++i) {
                        newArgs[i] = args[i].accept(this, inPattern);
                    }
            }
            return ctor.copyWithNewArgs(newArgs);
        }

        @Override
        public Term visit(Var x, Boolean inPattern) {
            if (inFormula) {
                Types.Type ty = env.get(x);
                assert ty != null;
                assert !ty.isVar();
                return lift(x, ty);
            }
            return x;
        }

        private Term lift(Term t, Types.Type ty) {
            assert inFormula;
            BuiltInConstructorSymbolBase base;
            List<Param> params = new ArrayList<>();
            if (ty.equals(BuiltInTypes.i32)) {
                base = BuiltInConstructorSymbolBase.BV_CONST;
                params.add(new Param(TypeIndex.make(32), ParamKind.NAT));
            } else if (ty.equals(BuiltInTypes.i64)) {
                base = BuiltInConstructorSymbolBase.BV_BIG_CONST;
                params.add(new Param(TypeIndex.make(64), ParamKind.NAT));
            } else if (ty.equals(BuiltInTypes.fp32)) {
                base = BuiltInConstructorSymbolBase.FP_CONST;
                params.add(new Param(TypeIndex.make(8), ParamKind.NAT));
                params.add(new Param(TypeIndex.make(24), ParamKind.NAT));
            } else if (ty.equals(BuiltInTypes.fp64)) {
                base = BuiltInConstructorSymbolBase.FP_BIG_CONST;
                params.add(new Param(TypeIndex.make(11), ParamKind.NAT));
                params.add(new Param(TypeIndex.make(53), ParamKind.NAT));
            } else {
                return t;
            }
            ConstructorSymbol sym = ParameterizedConstructorSymbol.mk(base, params);
            return Constructors.make(sym, Terms.singletonArray(t));
        }

        @Override
        public Term visit(Constructor ctor, Boolean inPattern) {
            ConstructorSymbol sym = ctor.getSymbol();
            if (sym instanceof BuiltInConstructorSymbol) {
                return handleBuiltInConstructor(ctor, inPattern);
            } else if (sym instanceof ParameterizedConstructorSymbol) {
                return handleParameterizedConstructor(ctor, inPattern);
            }

            Term[] args = ctor.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = args[i].accept(this, inPattern);
            }
            return ctor.copyWithNewArgs(newArgs);
        }

        @Override
        public Term visit(Primitive<?> p, Boolean inPattern) {
            if (!inFormula) {
                return p;
            }
            BuiltInConstructorSymbolBase base;
            List<Param> params = new ArrayList<>();
            if (p instanceof I32) {
                base = BuiltInConstructorSymbolBase.BV_CONST;
                params.add(new Param(TypeIndex.make(32), ParamKind.NAT));
            } else if (p instanceof I64) {
                base = BuiltInConstructorSymbolBase.BV_BIG_CONST;
                params.add(new Param(TypeIndex.make(64), ParamKind.NAT));
            } else if (p instanceof FP32) {
                base = BuiltInConstructorSymbolBase.FP_CONST;
                params.add(new Param(TypeIndex.make(8), ParamKind.NAT));
                params.add(new Param(TypeIndex.make(24), ParamKind.NAT));
            } else if (p instanceof FP64) {
                base = BuiltInConstructorSymbolBase.FP_BIG_CONST;
                params.add(new Param(TypeIndex.make(11), ParamKind.NAT));
                params.add(new Param(TypeIndex.make(53), ParamKind.NAT));
            } else {
                return p;
            }
            ConstructorSymbol sym = ParameterizedConstructorSymbol.mk(base, params);
            return Constructors.make(sym, Terms.singletonArray(p));
        }

        @Override
        public Term visit(Expr e, Boolean inPattern) {
            assert !inPattern;
            return e.accept(exprRewriter, null);
        }

    };

    private final ExprVisitor<Void, Term> exprRewriter = new ExprVisitor<Void, Term>() {

        @Override
        public Term visit(MatchExpr matchExpr, Void in) {
            Term newScrutinee = matchExpr.getMatchee().accept(termRewriter, false);
            List<MatchClause> newClauses = new ArrayList<>();
            for (MatchClause cl : matchExpr) {
                Term newLhs = cl.getLhs().accept(termRewriter, true);
                Term newRhs = cl.getRhs().accept(termRewriter, false);
                newClauses.add(MatchClause.make(newLhs, newRhs));
            }
            return MatchExpr.make(newScrutinee, newClauses);
        }

        @Override
        public Term visit(FunctionCall funcCall, Void in) {
            Term[] args = funcCall.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = args[i].accept(termRewriter, false);
            }
            return funcCall.copyWithNewArgs(newArgs);
        }

        @Override
        public Term visit(LetFunExpr funcDefs, Void in) {
            Set<NestedFunctionDef> newDefs = new HashSet<>();
            for (NestedFunctionDef def : funcDefs.getDefs()) {
                newDefs.add(NestedFunctionDef.make(def.getSymbol(), def.getParams(),
                        def.getBody().accept(termRewriter, false)));
            }
            Term newBody = funcDefs.getLetBody().accept(termRewriter, false);
            return LetFunExpr.make(newDefs, newBody);
        }

        @Override
        public Term visit(Fold fold, Void in) {
            Term[] args = fold.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = args[i].accept(termRewriter, false);
            }
            return Fold.mk(fold.getFunction(), newArgs, funcFactory);
        }

    };

}
