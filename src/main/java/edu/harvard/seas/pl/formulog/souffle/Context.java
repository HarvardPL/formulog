package edu.harvard.seas.pl.formulog.souffle;

import edu.harvard.seas.pl.formulog.ast.BoolTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.souffle.ast.SFunctorBody;
import edu.harvard.seas.pl.formulog.souffle.ast.SRule;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

public class Context {

    private final Map<String, AtomicInteger> funcSuffixMemo = new ConcurrentHashMap<>();
    private static final String functionPrefix = "formulog::functions::";
    private final Map<Term, Integer> constantMemo = new LinkedHashMap<>();
    private int constantCounter = 0;
    private final Map<String, SFunctorBody> functorBody = new ConcurrentHashMap<>();

    public Context() {
        lookupConstant(BoolTerm.mkFalse());
        lookupConstant(BoolTerm.mkTrue());
    }

    public String lookupRelation(RelationSymbol sym) {
        return mangle(sym);
    }

    public String lookupFunction(FunctionSymbol sym, boolean qualify) {
        String s = mangle(sym);
        if (qualify) {
            return functionPrefix + s;
        }
        return s;
    }

    public String freshFunctionName(String prefix) {
        int n = Util.lookupOrCreate(funcSuffixMemo, prefix, AtomicInteger::new).getAndIncrement();
        return prefix + "_" + n;
    }

    public synchronized int lookupConstant(Term t) {
        assert t.isGround() && !t.containsUnevaluatedTerm();
        Integer id = constantMemo.get(t);
        if (id == null) {
            id = constantCounter++;
            constantMemo.put(t, id);
        }
        return id;
    }

    public void registerFunctorBody(String functor, SFunctorBody body) {
        SFunctorBody other = functorBody.putIfAbsent(functor, body);
        assert other == null;
    }

    public Set<Pair<String, SFunctorBody>> getFunctors() {
        Set<Pair<String, SFunctorBody>> s = new HashSet<>();
        for (Map.Entry<String, SFunctorBody> e : functorBody.entrySet()) {
            s.add(new Pair<>(e.getKey(), e.getValue()));
        }
        return Collections.unmodifiableSet(s);
    }

    private String mangle(Symbol sym) {
        return sym.toString().replaceAll("<>,:", "_") + "_";
    }

}
