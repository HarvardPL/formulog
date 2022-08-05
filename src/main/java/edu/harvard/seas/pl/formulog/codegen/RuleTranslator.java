package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.ast.*;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.*;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.*;

import java.util.*;
import java.util.stream.Collectors;

public class RuleTranslator {

    private final CodeGenContext ctx;

    public RuleTranslator(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    public List<SRule> translate(BasicProgram prog) throws CodeGenException {
        checkStratification(prog);
        List<SRule> l = new ArrayList<>();
        Worker worker = new Worker(prog);
        for (RelationSymbol sym : prog.getRuleSymbols()) {
            for (BasicRule r : prog.getRules(sym)) {
                l.add(worker.translate(r));
            }
        }
        l.addAll(worker.createProjectionRules());
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

    private class Worker {

        private final BasicProgram prog;
        private Map<Var, Integer> varCount;
        private final Set<Pair<RelationSymbol, List<Boolean>>> projections = new HashSet<>();

        public Worker(BasicProgram prog) {
            this.prog = prog;
        }

        private SRule translate(BasicRule br) throws CodeGenException {
            SimpleRule sr;
            try {
                ValidRule vr = ValidRule.make(br, (_lit, _vars) -> 1);
                sr = SimpleRule.make(vr, prog.getFunctionCallFactory());
                varCount = sr.countVariables();
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
                    List<STerm> translatedArgs = args.stream().map(Worker.this::translate).collect(Collectors.toList());
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
                    List<STerm> args = Arrays.stream(predicate.getArgs()).map(Worker.this::translate).
                            collect(Collectors.toList());
                    SLit lit;
                    if (predicate.isNegated()) {
                        lit = handleNegatedPredicate(predicate, args);
                    } else {
                        String symbol = ctx.lookupRepr(predicate.getSymbol());
                        lit = new SAtom(symbol, args, false);
                    }
                    return Collections.singletonList(lit);
                }
            }, null);
        }

        private SLit handleNegatedPredicate(SimplePredicate predicate, List<STerm> souffleArgs) {
            List<Boolean> projection = new ArrayList<>();
            int ignoredCount = 0;
            var args = predicate.getArgs();
            for (Term arg : args) {
                if (arg instanceof Var && varCount.get((Var) arg) == 1) {
                    ignoredCount++;
                    projection.add(false);
                } else {
                    projection.add(true);
                }
            }
            RelationSymbol sym = predicate.getSymbol();
            if (ignoredCount == 0) {
                return new SAtom(ctx.lookupRepr(sym), souffleArgs, true);
            }
            projections.add(new Pair<>(predicate.getSymbol(), projection));
            List<STerm> newArgs = new ArrayList<>();
            for (int i = 0; i < souffleArgs.size(); ++i) {
                if (projection.get(i)) {
                    newArgs.add(souffleArgs.get(i));
                }
            }
            return new SAtom(createProjectionSymbol(sym, projection), newArgs, true);
        }

        private String createProjectionSymbol(RelationSymbol sym, List<Boolean> projection) {
            StringBuilder sb = new StringBuilder();
            sb.append("CODEGEN_PROJECT_");
            sb.append(ctx.lookupRepr(sym));
            for (Boolean retain : projection) {
                sb.append(retain ? "1" : "0");
            }
            return sb.toString();
        }

        private SFunctorCall liftToFunctor(Term t) {
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
                    return liftToFunctor(c);
                }

                @Override
                public STerm visit(Primitive<?> p, Void in) {
                    return liftToFunctor(p);
                }

                @Override
                public STerm visit(Expr e, Void in) {
                    return liftToFunctor(e);
                }
            }, null);
        }

        List<SRule> createProjectionRules() {
            List<SRule> l = new ArrayList<>();
            for (var p : projections) {
                l.add(createProjection(p.fst(), p.snd()));
            }
            return l;
        }

        private SRule createProjection(RelationSymbol sym, List<Boolean> projection) {
            List<STerm> headArgs = new ArrayList<>();
            List<STerm> bodyArgs = new ArrayList<>();
            for (int i = 0; i < sym.getArity(); ++i) {
                STerm arg = new SVar(Var.fresh("x" + i));
                bodyArgs.add(arg);
                if (projection.get(i)) {
                    headArgs.add(arg);
                }
            }
            String projSym = createProjectionSymbol(sym, projection);
            SLit head = new SAtom(projSym, headArgs, false);
            SLit bodyAtom = new SAtom(ctx.lookupRepr(sym), bodyArgs, false);
            ctx.registerCustomRelation(projSym, headArgs.size(), SRuleMode.INTERMEDIATE);
            return new SRule(head, bodyAtom);
        }
    }

}
