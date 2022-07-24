package edu.harvard.seas.pl.formulog.souffle;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.souffle.ast.CVar;
import edu.harvard.seas.pl.formulog.util.Util;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

public class FunctionContext {

    private final Map<Var, CVar> m = new HashMap<>();
    private final AtomicInteger cnt = new AtomicInteger();
    private final AtomicInteger tmpCnt = new AtomicInteger();

    public CVar lookupOrCreate(Var x) {
        return Util.lookupOrCreate(m, x, () -> new CVar("x" + cnt.getAndIncrement()));
    }

    public CVar freshVar() {
        return new CVar("t" + tmpCnt.getAndIncrement());
    }

}
