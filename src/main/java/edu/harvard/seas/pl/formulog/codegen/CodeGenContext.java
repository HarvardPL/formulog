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

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.SymbolBase;
import edu.harvard.seas.pl.formulog.util.Util;

public class CodeGenContext {

	private final Map<ConstructorSymbol, String> ctorSymToRepr = new ConcurrentHashMap<>();
	private final Map<FunctionSymbol, String> funcSymToRepr = new ConcurrentHashMap<>();
	private final Map<SymbolBase, AtomicInteger> cnts = new ConcurrentHashMap<>();
	private final Map<RelationSymbol, Relation> rels = new ConcurrentHashMap<>();
	private final AtomicInteger id = new AtomicInteger();

	private final SemiNaiveEvaluation eval;

	public CodeGenContext(SemiNaiveEvaluation eval) {
		this.eval = eval;
	}

	public SemiNaiveEvaluation getEval() {
		return eval;
	}
	
	public void registerRelation(RelationSymbol sym, Relation rel) {
		Relation rel2 = rels.put(sym, rel);
		assert rel2 == null;
	}
	
	public Relation lookupRelation(RelationSymbol sym) {
		Relation rel = rels.get(sym);
		assert rel != null : sym;
		return rel;
	}
	
	public String lookupRepr(ConstructorSymbol sym) {
		String repr = ctorSymToRepr.get(sym);
		if (repr == null) {
			repr = sym.toString();
			if (sym instanceof ParameterizedSymbol) {
				assert ((ParameterizedSymbol) sym).isGround();
				SymbolBase base = ((ParameterizedSymbol) sym).getBase();
				int n = Util.lookupOrCreate(cnts, base, () -> new AtomicInteger()).getAndIncrement();
				repr = base + "_" + n;
			}
			String repr2 = ctorSymToRepr.putIfAbsent(sym, repr);
			if (repr2 != null) {
				repr = repr2;
			}
		}
		return repr;
	}
	
	public String lookupRepr(FunctionSymbol sym) {
		String repr = funcSymToRepr.get(sym);
		assert repr != null : sym;
		return "funcs::" + repr;
	}
	
	public void register(FunctionSymbol sym, String repr) {
		String repr2 = funcSymToRepr.put(sym, repr);
		assert repr2 == null || repr2.equals(repr);
	}

	public String newId(String prefix) {
		return prefix + id.getAndIncrement(); 
	}

}
