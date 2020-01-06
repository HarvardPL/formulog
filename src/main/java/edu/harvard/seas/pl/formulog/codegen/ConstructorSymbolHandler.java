package edu.harvard.seas.pl.formulog.codegen;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Set;
import java.util.TreeSet;

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolComparator;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;

public class ConstructorSymbolHandler {

	private final CodeGenContext ctx;
	private final Set<ConstructorSymbol> symbols = new TreeSet<>(SymbolComparator.INSTANCE);

	public ConstructorSymbolHandler(CodeGenContext ctx) {
		this.ctx = ctx;
	}
	
	public void getConstructorsFromTypes(Set<TypeSymbol> syms) {
		for (TypeSymbol sym : syms) {
			if (!sym.isAlias()) {
				getConstructorsFromType(AlgebraicDataType.makeWithFreshArgs(sym));
			}
		}
	}

	private void getConstructorsFromType(AlgebraicDataType type) {
		if (type.hasConstructors()) {
			for (ConstructorScheme cs : type.getConstructors()) {
				ConstructorSymbol sym = cs.getSymbol();
				assert !(sym instanceof ParameterizedSymbol);
				ctx.lookupRepr(sym);
				symbols.add(sym);
				// XXX Need to do getters and checkers
			}
		}
	}

	public void print(File outDir) throws IOException {
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("Symbol.hpp");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(outDir.toPath().resolve("Symbol.hpp").toFile())) {
			String line;
			while (!(line = br.readLine()).equals("/* INSERT 0 */")) {
				out.println(line);
			}
			for (ConstructorSymbol sym : symbols) {
				out.print("  ");
				out.println(ctx.lookupRepr(sym) + ",");
			}
			while (!(line = br.readLine()).equals("/* INSERT 1 */")) {
				out.println(line);
			}
			for (ConstructorSymbol sym : symbols) {
				out.print("    case Symbol::");
				String repr = ctx.lookupRepr(sym);
				out.print(repr);
				out.print(": return out << \"");
				out.print(repr);
				out.println("\";");
			}
			while ((line = br.readLine()) != null) {
				out.println(line);
			}
			out.flush();
		}
		
	}

}
