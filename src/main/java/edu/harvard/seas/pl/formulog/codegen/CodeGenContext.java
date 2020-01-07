package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * FormuLog
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

import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveSymbol;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveSymbolType;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.SymbolBase;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class CodeGenContext implements Iterable<Pair<Symbol, String>> {

	private final Map<Symbol, String> symToRepr = new ConcurrentHashMap<>();
	private final Map<String, Symbol> reprToSym = new ConcurrentHashMap<>();
	private final Map<SymbolBase, AtomicInteger> cnts = new ConcurrentHashMap<>();
	private final Map<Pair<RelationSymbol, Integer>, CppIndex> rels = new ConcurrentHashMap<>();

	private final SemiNaiveEvaluation eval;

	public CodeGenContext(SemiNaiveEvaluation eval) {
		this.eval = eval;
	}

	public SemiNaiveEvaluation getEval() {
		return eval;
	}
	
	public CppIndex lookupIndex(RelationSymbol sym, int idx) {
		return Util.lookupOrCreate(rels, new Pair<>(sym, idx), () -> BTreeIndex.mk(sym, idx, this));
	}

	public String lookupRelationName(RelationSymbol sym, int idx) {
		assert idx >= 0;
		if (sym instanceof SemiNaiveSymbol) {
			SemiNaiveSymbol sym2 = (SemiNaiveSymbol) sym;
			assert sym2.getSemiNaiveSymbolType().equals(SemiNaiveSymbolType.DELTA);
			return lookupRepr(sym2.getBaseSymbol()) + "_delta_" + idx;
		}
		return lookupRepr(sym) + "_" + idx;
	}

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
