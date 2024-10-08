/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2020-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.codegen;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamKind;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Util;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;

public class CodeGen {

  private final BasicProgram prog;
  private final File outDir;

  public CodeGen(BasicProgram prog, File outDir) {
    this.prog = prog;
    this.outDir = outDir;
  }

  public void go() throws IOException, URISyntaxException, CodeGenException {
    CodeGenContext ctx = new CodeGenContext(prog);
    // Make sure that we generate a symbol for SMT variables (assumed in the C++
    // runtime code)
    ParameterizedConstructorSymbol sym =
        GlobalSymbolManager.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_VAR)
            .copyWithNewArgs(
                new Param(BuiltInTypes.bool, ParamKind.ANY_TYPE),
                new Param(BuiltInTypes.bool, ParamKind.PRE_SMT_TYPE));
    String repr = ctx.lookupRepr(sym);
    assert repr.equals("Symbol::smt_var__bool__bool") : repr;

    copy("CMakeLists.txt");
    copySrc("time.hpp");
    copySrc("ConcurrentHashMap.hpp");
    new FuncsHpp(ctx).gen(outDir);
    new MainCpp(ctx).gen(outDir);
    new SouffleCodeGen(ctx).gen(outDir);
    copySrc("smt_solver.h");
    copySrc("smt_solver.cpp");
    copySrc("smt_shim.h");
    new SmtShimCpp(ctx).gen(outDir);
    copySrc("smt_parser.hpp");
    new SmtParserCpp(ctx).gen(outDir);
    copySrc("Type.hpp");
    new TypeCpp(ctx).gen(outDir);
    copySrc("Term.hpp");
    new TermCpp(ctx).gen(outDir);
    copySrc("Tuple.hpp");
    copySrc("parser.hpp");
    copySrc("parser.cpp");
    new SymbolHpp(ctx).gen(outDir);
    new SymbolCpp(ctx).gen(outDir);
    copySrc("globals.h");
    copySrc("set.cpp");
    copySrc("set.hpp");
  }

  private void copy(String name) throws IOException {
    var inFile = Path.of("codegen", name).toString();
    try (InputStream is = getClass().getClassLoader().getResourceAsStream(inFile)) {
      assert is != null : name;
      Files.copy(is, outDir.toPath().resolve(name), StandardCopyOption.REPLACE_EXISTING);
    }
  }

  private void copySrc(String name) throws IOException {
    copy(Path.of("src", name).toString());
  }

  public static void main(String[] args) throws Exception {
    if (args.length != 1) {
      throw new IllegalArgumentException("Expected a single argument (the Formulog source file)");
    }
    main(new File(args[0]), new File("codegen"));
  }

  public static void main(File file, File outDir) throws Exception {
    Program<UserPredicate, BasicRule> prog;
    try (FileReader fr = new FileReader(file)) {
      prog = new Parser().parse(fr);
    }
    WellTypedProgram wtp = new TypeChecker(prog).typeCheck();
    MagicSetTransformer mst = new MagicSetTransformer(wtp);
    BasicProgram magicProg =
        mst.transform(Configuration.useDemandTransformation, Configuration.restoreStratification);
    File srcDir = outDir.toPath().resolve("src").toFile();
    srcDir.mkdirs();
    Util.clean(srcDir, false);
    new CodeGen(magicProg, outDir).go();
  }
}
