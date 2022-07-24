package edu.harvard.seas.pl.formulog.souffle;

import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.souffle.ast.*;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class RuleTranslator {

    private final Context ctx;

    public RuleTranslator(Context ctx_) {
        ctx = ctx_;
    }

    public List<SRule> translate(BasicProgram prog) throws SouffleGenException {
        checkStratification(prog);
        List<SRule> l = new ArrayList<>();
        for (RelationSymbol sym : prog.getRuleSymbols()) {
            for (BasicRule r : prog.getRules(sym)) {
                l.add(translate(r, prog));
            }
        }
        return l;
    }

    private void checkStratification(BasicProgram prog) throws SouffleGenException {
        Stratifier stratifier = new Stratifier(prog);
        List<Stratum> strats;
        try {
            strats = stratifier.stratify();
        } catch (InvalidProgramException e) {
            throw new SouffleGenException(e);
        }
        for (Stratum strat : strats) {
            if (strat.hasRecursiveNegationOrAggregation()) {
                throw new SouffleGenException("Cannot handle recursive negation or aggregation: " + strat);
            }
        }
    }

    private SRule translate(BasicRule br, BasicProgram prog) throws SouffleGenException {
        SimpleRule sr;
        try {
            ValidRule vr = ValidRule.make(br, (_lit, _vars) -> 1);
            sr = SimpleRule.make(vr, prog.getFunctionCallFactory());
        } catch (InvalidProgramException e) {
            throw new SouffleGenException(e);
        }
        SLit head = translate(sr.getHead());
        List<SLit> body = new ArrayList<>();
        for (int i = 0; i < sr.getBodySize(); ++i) {
            body.add(translate(sr.getBody(i)));
        }
        return new SRule(head, body);
    }

    private SLit translate(SimpleLiteral lit) {
        return lit.accept(new SimpleLiteralVisitor<Void, SLit>() {
            @Override
            public SLit visit(Assignment assignment, Void input) {
                STerm lhs = translate(assignment.getDef());
                STerm rhs = translate(assignment.getVal());
                return new SInfixBinaryOpAtom(lhs, "=", rhs);
            }

            @Override
            public SLit visit(Check check, Void input) {
                STerm lhs = translate(check.getLhs());
                STerm rhs = translate(check.getRhs());
                return new SInfixBinaryOpAtom(lhs, check.isNegated() ? "!=" : "=", rhs);
            }

            @Override
            public SLit visit(Destructor destructor, Void input) {
                Term scrutinee = destructor.getScrutinee();
                List<Var> args = new ArrayList<>(scrutinee.varSet());
                String functor = ctx.freshFunctionName("dtor");
                ctx.registerFunctorBody(functor, new SDestructorBody(args, scrutinee, destructor.getSymbol()));
                List<STerm> translatedArgs = args.stream().map(RuleTranslator.this::translate).collect(Collectors.toList());
                STerm lhs = new SFunctorCall(functor, translatedArgs);
                Var[] bindings = destructor.getBindings();
                List<STerm> vars = Arrays.stream(bindings).map(RuleTranslator.this::translate).collect(Collectors.toList());
                SList rhs = new SList(vars);
                return new SInfixBinaryOpAtom(lhs, "=", rhs);
            }

            @Override
            public SLit visit(SimplePredicate predicate, Void input) {
                String symbol = ctx.lookupRelation(predicate.getSymbol());
                List<STerm> args = Arrays.stream(predicate.getArgs()).map(RuleTranslator.this::translate).
                        collect(Collectors.toList());
                return new SAtom(symbol, args, predicate.isNegated());
            }
        }, null);
    }

    private SInt translateConstant(Term t) {
        return new SInt(ctx.lookupConstant(t));
    }

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
                if (c.isGround() && !c.containsUnevaluatedTerm()) {
                    return translateConstant(c);
                }
                return translateNonConstant(c);
            }

            @Override
            public STerm visit(Primitive<?> p, Void in) {
                return translateConstant(p);
            }

            @Override
            public STerm visit(Expr e, Void in) {
                return translateNonConstant(e);
            }
        }, null);
    }

}
