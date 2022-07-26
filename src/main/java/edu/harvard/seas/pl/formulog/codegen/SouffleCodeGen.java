package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.codegen.ast.souffle.*;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.util.List;

public class SouffleCodeGen {
    /*
    TODO:
    - [X] Define AST for terms
    - [X] Output rules
    - [ ] Output functions
        - [ ] Output functor declarations (.h file)
        - [ ] Output functors that Souffle calls (.cpp file)
        - [ ] Output user-defined functors (.cpp file, namespace formulog::functions::)
    - [ ] Output main file
        - [ ] Load program
        - [ ] Intize constants
        - [ ] Load relations
        - [ ] Run program
     - [ ] Add standard library functions
        - [ ] SMT stuff

     TODO later:
     - [ ] Generate SMT ADT declarations
     - [ ] Handle aggregates
     */

    private final CodeGenContext ctx;

    public SouffleCodeGen(CodeGenContext ctx) {
        this.ctx = ctx;
    }

    public void gen(File directory) throws CodeGenException, IOException {
        List<SRule> rules = new RuleTranslator(ctx).translate(ctx.getProgram());
        File dlFile = directory.toPath().resolve(Path.of("src", "formulog.dl")).toFile();
        emitDlFile(dlFile, rules);
        new FunctorCodeGen(ctx).emitFunctors(directory);
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
                declareRelation(sym);
                writer.print(".input ");
                writer.println(ctx.lookupRepr(sym));
            }
            for (RelationSymbol sym : ctx.getProgram().getRuleSymbols()) {
                declareRelation(sym);
                writer.print(".output ");
                writer.println(ctx.lookupRepr(sym));
            }
        }

        private void declareRelation(RelationSymbol sym) {
            writer.print(".decl ");
            writer.print(ctx.lookupRepr(sym));
            writer.print("(");
            for (int i = 0; i < sym.getArity(); ++i) {
                writer.print("x");
                writer.print(i);
                writer.print(":number");
                if (i < sym.getArity() - 1) {
                    writer.print(", ");
                }
            }
            writer.println(")");
        }

        public void declareFunctors() {
            writer.println(".functor nth(n:number, ref:number, arity:number):number stateful");
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
