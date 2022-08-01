package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.*;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.unification.EmptySubstitution;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class RuleTranslator {

    private final CodeGenContext ctx;

    public RuleTranslator(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    public List<SRule> translate(BasicProgram prog) throws CodeGenException {
        checkStratification(prog);
        List<SRule> l = new ArrayList<>();
        for (RelationSymbol sym : prog.getRuleSymbols()) {
            for (BasicRule r : prog.getRules(sym)) {
                l.add(translate(r, prog));
            }
        }
        return l;
    }

    private void checkStratification(BasicProgram prog) throws CodeGenException {
        Stratifier stratifier = new Stratifier(prog);
        List<Stratum> strats;
        try {
            strats = stratifier.stratify();
        } catch (InvalidProgramException e) {
            throw new CodeGenException(e);
        }
        for (Stratum strat : strats) {
            if (strat.hasRecursiveNegationOrAggregation()) {
                throw new CodeGenException("Cannot handle recursive negation or aggregation: " + strat);
            }
        }
    }

    private SRule translate(BasicRule br, BasicProgram prog) throws CodeGenException {
        SimpleRule sr;
        try {
            ValidRule vr = ValidRule.make(br, (_lit, _vars) -> 1);
            sr = SimpleRule.make(vr, prog.getFunctionCallFactory());
        } catch (InvalidProgramException e) {
            throw new CodeGenException(e);
        }
        List<SLit> headTrans = translate(sr.getHead());
        assert headTrans.size() == 1;
        SLit head = headTrans.get(0);
        List<SLit> body = new ArrayList<>();
        for (int i = 0; i < sr.getBodySize(); ++i) {
            body.addAll(translate(sr.getBody(i)));
        }
        return new SRule(head, body);
    }

    private List<SLit> translate(SimpleLiteral lit) {
        return lit.accept(new SimpleLiteralVisitor<Void, List<SLit>>() {
            @Override
            public List<SLit> visit(Assignment assignment, Void input) {
                STerm lhs = translate(assignment.getDef());
                STerm rhs = translate(assignment.getVal());
                return Collections.singletonList(new SInfixBinaryOpAtom(lhs, "=", rhs));
            }

            @Override
            public List<SLit> visit(Check check, Void input) {
                STerm lhs = translate(check.getLhs());
                STerm rhs = translate(check.getRhs());
                return Collections.singletonList(new SInfixBinaryOpAtom(lhs, check.isNegated() ? "!=" : "=", rhs));
            }

            @Override
            public List<SLit> visit(Destructor destructor, Void input) {
                Term scrutinee = destructor.getScrutinee();
                List<Var> args = new ArrayList<>(scrutinee.varSet());
                String functor = ctx.freshFunctionName("dtor");
                var dtor = new SDestructorBody(args, scrutinee, destructor.getSymbol());
                ctx.registerFunctorBody(functor, dtor);
                // ctx.register(dtor.getRetType());
                List<STerm> translatedArgs = args.stream().map(RuleTranslator.this::translate).collect(Collectors.toList());
                STerm lhs = new SFunctorCall(functor, translatedArgs);
                SVar recRef = new SVar(Var.fresh());
                List<SLit> l = new ArrayList<>();
                l.add(new SInfixBinaryOpAtom(lhs, "=", recRef));
                l.add(new SInfixBinaryOpAtom(recRef, "!=", new SInt(0)));
                int arity = destructor.getSymbol().getArity();
                Var[] bindings = destructor.getBindings();
                for (int i = 0; i < arity; ++i) {
                    SFunctorCall call = new SFunctorCall("nth", new SInt(i), recRef, new SInt(arity));
                    l.add(new SInfixBinaryOpAtom(translate(bindings[i]), "=", call));
                }
                return l;
            }

            @Override
            public List<SLit> visit(SimplePredicate predicate, Void input) {
                String symbol = ctx.lookupRepr(predicate.getSymbol());
                List<STerm> args = Arrays.stream(predicate.getArgs()).map(RuleTranslator.this::translate).
                        collect(Collectors.toList());
                return Collections.singletonList(new SAtom(symbol, args, predicate.isNegated()));
            }
        }, null);
    }

    /*
    private SInt translateConstant(Term t) {
        return new SInt(ctx.lookupConstant(t));
    }
     */

    private SFunctorCall translateNonConstant(Term t) {
        String functor = ctx.freshFunctionName("expr");
        List<Var> args = new ArrayList<>(t.varSet());
        ctx.registerFunctorBody(functor, new SExprBody(args, t));
        List<STerm> translatedArgs = args.stream().map(this::translate).collect(Collectors.toList());
        return new SFunctorCall(functor, translatedArgs);
    }

    private STerm translate(Term t) {
        return t.accept(new Terms.TermVisitor<Void, STerm>() {
            @Override
            public STerm visit(Var t, Void in) {
                return new SVar(t);
            }

            @Override
            public STerm visit(Constructor c, Void in) {
                /*
                if (c.isGround() && !c.containsUnevaluatedTerm()) {
                    return translateConstant(c);
                }
                 */
                return translateNonConstant(c);
            }

            @Override
            public STerm visit(Primitive<?> p, Void in) {
                /*
                return translateConstant(p);
                 */
                return translateNonConstant(p);
            }

            @Override
            public STerm visit(Expr e, Void in) {
                return translateNonConstant(e);
            }
        }, null);
    }

}
