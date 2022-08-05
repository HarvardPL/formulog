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

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SFunctorBody;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SIntListType;
import edu.harvard.seas.pl.formulog.symbols.*;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.SymbolBase;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

public class CodeGenContext {

    private final Map<ConstructorSymbol, String> ctorSymToRepr = new HashMap<>();
    private final Map<FunctionSymbol, String> funcSymToRepr = new HashMap<>();
    private final Map<SymbolBase, AtomicInteger> cnts = new HashMap<>();
    private final AtomicInteger id = new AtomicInteger();
    private final Map<String, SFunctorBody> functorBody = new ConcurrentHashMap<>();
    private final Map<String, AtomicInteger> funcSuffixMemo = new ConcurrentHashMap<>();
    private final Set<SIntListType> souffleTypes = new HashSet<>();
    private final Map<String, Integer> customRelations = new HashMap<>();

    private final BasicProgram prog;

    public CodeGenContext(BasicProgram prog) {
        this.prog = prog;
        new Worker().go();
    }

    public BasicProgram getProgram() {
        return prog;
    }

    public Set<ConstructorSymbol> getConstructorSymbols() {
        return Collections.unmodifiableSet(ctorSymToRepr.keySet());
    }

    public synchronized String lookupUnqualifiedRepr(ConstructorSymbol sym) {
        String repr = ctorSymToRepr.get(sym);
        if (repr == null) {
            repr = CodeGenUtil.mkName(sym);
            if (sym instanceof ParameterizedSymbol) {
                assert ((ParameterizedSymbol) sym).isGround();
                SymbolBase base = ((ParameterizedSymbol) sym).getBase();
                int n = Util.lookupOrCreate(cnts, base, AtomicInteger::new).getAndIncrement();
                repr = base + "_" + n;
            }
            String repr2 = ctorSymToRepr.putIfAbsent(sym, repr);
            assert repr2 == null;
        }
        return repr;
    }

    public synchronized String lookupRepr(ConstructorSymbol sym) {
        return "Symbol::" + lookupUnqualifiedRepr(sym);
    }

    public synchronized String lookupRepr(FunctionSymbol sym) {
        String repr = funcSymToRepr.get(sym);
        assert repr != null : sym;
        return "funcs::" + repr;
    }

    public synchronized String lookupRepr(RelationSymbol sym) {
        return sym + "_";
    }

    public synchronized void register(FunctionSymbol sym, String repr) {
        String repr2 = funcSymToRepr.put(sym, repr);
        assert repr2 == null || repr2.equals(repr);
    }

    public synchronized void register(SIntListType type) {
        souffleTypes.add(type);
    }

    public synchronized Set<SIntListType> getSouffleTypes() {
        return Collections.unmodifiableSet(souffleTypes);
    }

    public String newId(String prefix) {
        return prefix + id.getAndIncrement();
    }

    public String freshFunctionName(String prefix) {
        int n = Util.lookupOrCreate(funcSuffixMemo, prefix, AtomicInteger::new).getAndIncrement();
        return prefix + "_" + n;
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

    public Set<Pair<String, Integer>> getCustomRelations() {
        return customRelations.entrySet().stream().map(e -> new Pair<>(e.getKey(), e.getValue())).collect(Collectors.toSet());
    }

    public void registerCustomRelation(String name, Integer arity) {
        Integer other = customRelations.put(name, arity);
        assert other == null || other.equals(arity);
    }

    private class Worker {

        public Worker() {
        }

        public void go() {
            processTypes(prog.getTypeSymbols());
            for (ConstructorSymbol sym : BuiltInConstructorSymbol.values()) {
                lookupRepr(sym);
            }
        }

        private void processTypes(Set<TypeSymbol> typeSymbols) {
            for (TypeSymbol sym : typeSymbols) {
                if (!sym.isAlias()) {
                    processType(AlgebraicDataType.makeWithFreshArgs(sym));
                }
            }
        }

        private void processType(AlgebraicDataType type) {
            if (type.hasConstructors()) {
                for (ConstructorScheme cs : type.getConstructors()) {
                    ConstructorSymbol sym = cs.getSymbol();
                    lookupRepr(sym);
                }
            }
        }

    }

}
