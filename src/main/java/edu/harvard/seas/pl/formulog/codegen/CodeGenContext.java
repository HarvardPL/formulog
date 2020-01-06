package edu.harvard.seas.pl.formulog.codegen;

import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.SymbolBase;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class CodeGenContext implements Iterable<Pair<Symbol, String>> {

	private final Map<Symbol, String> symToRepr = new ConcurrentHashMap<>();
	private final Map<String, Symbol> reprToSym = new ConcurrentHashMap<>();
	private final Map<SymbolBase, AtomicInteger> cnts = new ConcurrentHashMap<>();

	public String lookupRepr(Symbol sym) {
		String repr = symToRepr.get(sym);
		if (repr == null) {
			repr = sym.toString();
			if (sym instanceof ParameterizedSymbol) {
				assert ((ParameterizedSymbol) sym).isGround();
				SymbolBase base = ((ParameterizedSymbol) sym).getBase();
				int n = Util.lookupOrCreate(cnts, base, () -> new AtomicInteger()).getAndIncrement();
				repr = base + "_" + n;
			}
			String repr2 = symToRepr.putIfAbsent(sym, repr);
			if (repr2 != null) {
				repr = repr2;
			} else {
				reprToSym.put(repr, sym);
			}
		}
		return repr;
	}

	public Symbol lookupSymbol(String repr) {
		Symbol sym = reprToSym.get(repr);
		assert sym != null : repr;
		return sym;
	}

	@Override
	public Iterator<Pair<Symbol, String>> iterator() {
		return new Iterator<Pair<Symbol, String>>() {

			private final Iterator<Map.Entry<Symbol, String>> it = symToRepr.entrySet().iterator();

			@Override
			public boolean hasNext() {
				return it.hasNext();
			}

			@Override
			public Pair<Symbol, String> next() {
				Map.Entry<Symbol, String> e = it.next();
				return new Pair<>(e.getKey(), e.getValue());
			}

		};
	}

}
