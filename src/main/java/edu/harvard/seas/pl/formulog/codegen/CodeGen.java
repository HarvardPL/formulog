package edu.harvard.seas.pl.formulog.codegen;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;

public class CodeGen {

	private final SemiNaiveEvaluation eval;
	private final File outDir;

	public CodeGen(SemiNaiveEvaluation eval, File outDir) {
		this.eval = eval;
		this.outDir = outDir;
	}

	public void go() throws IOException {
		SymbolContext ctx = new SymbolContext();
		ConstructorSymbolHandler csh = new ConstructorSymbolHandler(ctx);
		csh.getConstructorsFromTypes(eval.getInputProgram().getTypeSymbols());
		csh.print(outDir);
	}

	public static void main(String[] args) throws Exception {
		if (args.length != 1) {
			throw new IllegalArgumentException("Expected a single argument (the Formulog source file)");
		}
		Program<UserPredicate, BasicRule> prog;
		try (FileReader fr = new FileReader(args[0])) {
			prog = new Parser().parse(fr);
		}
		WellTypedProgram wtp = new TypeChecker(prog).typeCheck();
		SemiNaiveEvaluation eval = SemiNaiveEvaluation.setup(wtp, 4);
		File dir = new File("codegen");
		dir.mkdirs();
		new CodeGen(eval, dir).go();
	}

}
