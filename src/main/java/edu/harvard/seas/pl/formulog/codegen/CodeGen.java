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

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;

public class CodeGen {

    private final BasicProgram prog;
    private final File outDir;

    public CodeGen(BasicProgram prog, File outDir) {
        this.prog = prog;
        this.outDir = outDir;
    }

    public void go() throws IOException, URISyntaxException, CodeGenException {
        /*
        if (Configuration.minIndex) {
            throw new UnsupportedOperationException(
                    "We do not currently support code gen and optimal index selection (use flag -DminIndex=false).");
        }
         */
        //copy("Makefile");
        copy("CMakeLists.txt");
        CodeGenContext ctx = new CodeGenContext(prog);
        new RelsHpp(ctx).gen(outDir);
        new FuncsHpp(ctx).gen(outDir);
        new MainCpp(ctx).gen(outDir);
        new SouffleCodeGen(ctx).gen(outDir);
        copySrc("smt.hpp");
        new SmtCpp(ctx).gen(outDir);
        new TypeHpp(ctx).gen(outDir);
        copySrc("Term.hpp");
        new TermCpp(ctx).gen(outDir);
        copySrc("Tuple.hpp");
        copySrc("parser.hpp");
        new ParserCpp(ctx).gen(outDir);
        //new RulesMk().print(outDir);
        new SymbolHpp(ctx).gen(outDir);
        new SymbolCpp(ctx).gen(outDir);
        copySrc("globals.h");
        copySrc("globals.cpp");
    }

    private void copy(String name) throws IOException {
        /*
        String ext = name.substring(name.lastIndexOf('.') + 1);
        if (ext.equals("zip")) {
            copyZip(name);
            return;
        }
        */
        var inFile = Path.of("codegen", name).toString();
        try (InputStream is = getClass().getClassLoader().getResourceAsStream(inFile)) {
            assert is != null : name;
            Files.copy(is, outDir.toPath().resolve(name), StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private void copySrc(String name) throws IOException {
        copy(Path.of("src", name).toString());
    }

    /*
    private void copyZip(String name) throws IOException {
        try (InputStream is = getClass().getClassLoader().getResourceAsStream(name);
             ZipInputStream zis = new ZipInputStream(is)) {
            ZipEntry entry;
            while ((entry = zis.getNextEntry()) != null) {
                String fileName = entry.getName();
                Path dest = outDir.toPath().resolve(fileName);
                if (entry.isDirectory()) {
                    dest.toFile().mkdirs();
                } else {
                    Files.copy(zis, dest);
                }
                zis.closeEntry();
            }
        }
    }
    */

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new IllegalArgumentException("Expected a single argument (the Formulog source file)");
        }
        Program<UserPredicate, BasicRule> prog;
        try (FileReader fr = new FileReader(args[0])) {
            prog = new Parser().parse(fr);
        }
        WellTypedProgram wtp = new TypeChecker(prog).typeCheck();
        MagicSetTransformer mst = new MagicSetTransformer(wtp);
        BasicProgram magicProg = mst.transform(Configuration.useDemandTransformation,
                Configuration.restoreStratification);
        File dir = new File("codegen");
        File srcDir = dir.toPath().resolve("src").toFile();
        srcDir.mkdirs();
        Util.clean(srcDir, false);
        new CodeGen(magicProg, dir).go();
    }

}
