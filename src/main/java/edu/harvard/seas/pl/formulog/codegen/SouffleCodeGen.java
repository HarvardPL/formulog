package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.Configuration;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.codegen.ast.souffle.*;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.Stratum;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class SouffleCodeGen {

    private final CodeGenContext ctx;
    private static final String non_existent_input = "CODEGEN_IMPOSSIBLE_IN";
    private static final String non_existent_output = "CODEGEN_IMPOSSIBLE_OUT";
    private static final SAtom non_existent_input_atom = new SAtom(non_existent_input, Collections.emptyList(), false);

    public SouffleCodeGen(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    public void gen(File directory) throws CodeGenException, IOException {
        QueryPlanner qp = chooseQueryPlanner();
        Pair<List<SRule>, List<Stratum>> p = new RuleTranslator(ctx, qp).translate(ctx.getProgram());
        var rules = p.fst();
        ctx.registerCustomRelation(non_existent_input, 0, SRuleMode.INPUT);
        ctx.registerCustomRelation(non_existent_output, 0, SRuleMode.OUTPUT);
        rules.add(genRuleForRetainingInputRelations());
        rules.addAll(genRulesForEnforcingStratification(p.snd()));
        File dlFile = directory.toPath().resolve(Path.of("src", "formulog.dl")).toFile();
        emitDlFile(dlFile, rules);
        new FunctorCodeGen(ctx).emitFunctors(directory);
    }

    private QueryPlanner chooseQueryPlanner() throws CodeGenException {
        switch (Configuration.optimizationSetting) {
        case 0:
            return new NopQueryPlanner();
        case 5:
            return new DeltaFirstQueryPlanner(ctx);
        default:
            throw new CodeGenException(
                    "Unsupported optimization setting for codegen: " + Configuration.optimizationSetting);
        }
    }

    private void emitDlFile(File dlFile, List<SRule> rules) throws CodeGenException {
        PrintWriter writer;
        try {
            writer = new PrintWriter(dlFile);
        } catch (FileNotFoundException e) {
            throw new CodeGenException(e);
        }
        Worker worker = new Worker(writer);
        worker.declareTypes();
        writer.println();
        worker.declareRelations();
        writer.println();
        worker.declareFunctors();
        writer.println();
        for (SRule rule : rules) {
            writer.println(rule);
        }
        writer.close();
    }

    SRule genRuleForRetainingInputRelations() {
        SAtom head = new SAtom(non_existent_output, Collections.emptyList(), false);
        List<SLit> body = new ArrayList<>();
        body.add(non_existent_input_atom);
        for (RelationSymbol sym : ctx.getProgram().getFactSymbols()) {
            body.add(makeAtomWithDummyArgs(sym, false));
        }
        return new SRule(head, body);
    }

    private List<SRule> genRulesForEnforcingStratification(List<Stratum> strats) {
        if (strats.isEmpty()) {
            return Collections.emptyList();
        }
        List<SRule> l = new ArrayList<>();
        RelationSymbol firstRepr = strats.get(0).getPredicateSyms().iterator().next();
        var prevAtom = makeAtomWithDummyArgs(firstRepr, true);
        for (int i = 1; i < strats.size(); ++i) {
            RelationSymbol currRepr = strats.get(i).getPredicateSyms().iterator().next();
            var currAtom = makeAtomWithDummyArgs(currRepr, false);
            l.add(new SRule(currAtom, non_existent_input_atom, prevAtom));
            prevAtom = currAtom;
        }
        return l;
    }

    private SAtom makeAtomWithDummyArgs(RelationSymbol sym, boolean negated) {
        List<STerm> args = new ArrayList<>();
        for (int i = 0; i < sym.getArity(); ++i) {
            args.add(new SInt(0));
        }
        return new SAtom(ctx.lookupRepr(sym), args, negated);
    }

    private class Worker {

        private final PrintWriter writer;

        public Worker(PrintWriter writer) {
            this.writer = writer;
        }

        public void declareTypes() {
            for (SIntListType ty : ctx.getSouffleTypes()) {
                writer.print(".type ");
                writer.print(ty.getName());
                writer.print(" = ");
                writer.println(ty.getDef());
            }
        }

        public void declareRelations() {
            for (RelationSymbol sym : ctx.getProgram().getFactSymbols()) {
                declareRelation(sym, SRuleMode.INPUT);
            }
            for (RelationSymbol sym : ctx.getProgram().getRuleSymbols()) {
                declareRelation(sym, SRuleMode.OUTPUT);
            }
            for (Pair<String, Pair<Integer, SRuleMode>> e : ctx.getCustomRelations()) {
                declareRelation(e.fst(), e.snd().fst(), e.snd().snd());
            }
        }

        private void declareRelation(String name, int arity, SRuleMode mode) {
            writer.print(".decl ");
            writer.print(name);
            writer.print("(");
            for (int i = 0; i < arity; ++i) {
                writer.print("x");
                writer.print(i);
                writer.print(":number");
                if (i < arity - 1) {
                    writer.print(", ");
                }
            }
            writer.println(")");
            switch (mode) {
            case INPUT:
                writer.print(".input ");
                break;
            case OUTPUT:
                writer.print(".output ");
                break;
            case INTERMEDIATE:
                return;
            }
            writer.println(name);
        }

        private void declareRelation(RelationSymbol sym, SRuleMode mode) {
            declareRelation(ctx.lookupRepr(sym), sym.getArity(), mode);
        }

        public void declareFunctors() {
            writer.println(".functor nth(n:number, ref:number, check:number):number");
            for (Pair<String, SFunctorBody> p : ctx.getFunctors()) {
                String name = p.fst();
                SFunctorBody body = p.snd();
                declareFunctor(name, body);
            }
        }

        private void declareFunctor(String name, SFunctorBody body) {
            writer.print(".functor ");
            writer.print(name);
            writer.print("(");
            for (int i = 0; i < body.getArity(); ++i) {
                writer.print("x");
                writer.print(i);
                writer.print(":number");
                if (i < body.getArity() - 1) {
                    writer.print(", ");
                }
            }
            writer.print("):");
            writer.print(body.getRetType());
            if (body.isStateful()) {
                writer.print(" stateful");
            }
            writer.println();
        }

    }

}
