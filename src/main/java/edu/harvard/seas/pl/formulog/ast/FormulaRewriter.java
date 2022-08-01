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

import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamKind;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;

import java.util.*;

public class FormulaRewriter {

    private final FunctionCallFactory funcFactory;
    private final Map<Var, Types.Type> env;

    public FormulaRewriter(FunctionCallFactory funcFactory, Map<Var, Types.Type> env) {
        this.funcFactory = funcFactory;
        this.env = env;
    }

    public Term rewrite(Term t) {
        return t.accept(termRewriter, false);
    }

    private final TermVisitor<Boolean, Term> termRewriter = new TermVisitor<>() {

        private Term handleBuiltInConstructor(Constructor ctor, boolean inFormula) {
            BuiltInConstructorSymbol sym = (BuiltInConstructorSymbol) ctor.getSymbol();
            Term[] args = ctor.getArgs();
            Term[] newArgs = new Term[args.length];
            switch (sym) {
                case ENTER_FORMULA: {
                    return args[0].accept(this, true);
                }
                case EXIT_FORMULA: {
                    return args[0].accept(this, false);
                }
                case INT_CONST:
                case INT_BIG_CONST: {
                    assert args.length == 1;
                    newArgs[0] = args[0].accept(this, false);
                }
                break;
                default:
                    for (int i = 0; i < args.length; ++i) {
                        newArgs[i] = args[i].accept(this, inFormula);
                    }
            }
            return ctor.copyWithNewArgs(newArgs);
        }

        private Term handleParameterizedConstructor(Constructor ctor, boolean inFormula) {
            ParameterizedConstructorSymbol sym = (ParameterizedConstructorSymbol) ctor.getSymbol();
            Term[] args = ctor.getArgs();
            Term[] newArgs = new Term[args.length];
            switch (sym.getBase()) {
                case BV_CONST:
                case BV_BIG_CONST:
                case FP_CONST:
                case FP_BIG_CONST: {
                    assert args.length == 1;
                    newArgs[0] = args[0].accept(this, false);
                }
                break;
                case BV_EXTRACT: {
                    assert args.length == 3;
                    newArgs[0] = args[0].accept(this, inFormula);
                    newArgs[1] = args[1].accept(this, false);
                    newArgs[2] = args[2].accept(this, false);
                }
                break;
                default:
                    for (int i = 0; i < args.length; ++i) {
                        newArgs[i] = args[i].accept(this, inFormula);
                    }
            }
            return ctor.copyWithNewArgs(newArgs);
        }

        @Override
        public Term visit(Var x, Boolean inFormula) {
            if (inFormula) {
                Types.Type ty = env.get(x);
                assert ty != null;
                assert !ty.isVar();
                return lift(x, ty);
            }
            return x;
        }

        private Term lift(Term t, Types.Type ty) {
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
        public Term visit(Constructor ctor, Boolean inFormula) {
            ConstructorSymbol sym = ctor.getSymbol();
            if (sym instanceof BuiltInConstructorSymbol) {
                return handleBuiltInConstructor(ctor, inFormula);
            } else if (sym instanceof ParameterizedConstructorSymbol) {
                return handleParameterizedConstructor(ctor, inFormula);
            }

            Term[] args = ctor.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = args[i].accept(this, inFormula);
            }
            return ctor.copyWithNewArgs(newArgs);
        }

        @Override
        public Term visit(Primitive<?> p, Boolean inFormula) {
            if (!inFormula) {
                return p;
            }
            return lift(p, p.getType());
        }

        @Override
        public Term visit(Expr e, Boolean inFormula) {
            assert !inFormula || (e instanceof FunctionCall && ((FunctionCall) e).getArgs().length == 0);
            return e.accept(exprRewriter, null);
        }

    };

    private final ExprVisitor<Void, Term> exprRewriter = new ExprVisitor<>() {

        @Override
        public Term visit(MatchExpr matchExpr, Void in) {
            Term newScrutinee = rewrite(matchExpr.getMatchee());
            List<MatchClause> newClauses = new ArrayList<>();
            for (MatchClause cl : matchExpr) {
                Term newLhs = rewrite(cl.getLhs());
                Term newRhs = rewrite(cl.getRhs());
                newClauses.add(MatchClause.make(newLhs, newRhs));
            }
            return MatchExpr.make(newScrutinee, newClauses);
        }

        @Override
        public Term visit(FunctionCall funcCall, Void in) {
            Term[] args = funcCall.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = rewrite(args[i]);
            }
            return funcCall.copyWithNewArgs(newArgs);
        }

        @Override
        public Term visit(LetFunExpr funcDefs, Void in) {
            Set<NestedFunctionDef> newDefs = new HashSet<>();
            for (NestedFunctionDef def : funcDefs.getDefs()) {
                newDefs.add(NestedFunctionDef.make(def.getSymbol(), def.getParams(),
                        rewrite(def.getBody())));
            }
            Term newBody = rewrite(funcDefs.getLetBody());
            return LetFunExpr.make(newDefs, newBody);
        }

        @Override
        public Term visit(Fold fold, Void in) {
            Term[] args = fold.getArgs();
            Term[] newArgs = new Term[args.length];
            for (int i = 0; i < args.length; ++i) {
                newArgs[i] = rewrite(args[i]);
            }
            return Fold.mk(fold.getFunction(), newArgs, funcFactory);
        }

    };

}
