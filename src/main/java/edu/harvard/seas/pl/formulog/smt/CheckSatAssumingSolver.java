package edu.harvard.seas.pl.formulog.smt;

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

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParamKind;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.util.Pair;

public class CheckSatAssumingSolver extends AbstractSmtLibSolver {

	private final Map<SmtLibTerm, SolverVariable> indicatorVars = new ConcurrentHashMap<>();
	private int nextVarId;

	private void clearCache() {
		if (Configuration.timeSmt) {
			Configuration.recordCsaCacheClear(solverId);
		}
		indicatorVars.clear();
		shim.pop();
		shim.push();
	}

	public Set<SmtLibTerm> getCache() {
		return indicatorVars.keySet();
	}

	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(List<SmtLibTerm> formula, String id) {
		ByteArrayOutputStream baos = null;
		if (debugShim != null) {
			baos = new ByteArrayOutputStream();
			debugShim.redirectOutput(new PrintWriter(baos));
		}
		int oldSize = indicatorVars.size();
		int hits = 0;
		int adds = 0;
		Set<SolverVariable> xs = new HashSet<>();
		for (SmtLibTerm conjunct : formula) {
			SolverVariable x = indicatorVars.get(conjunct);
			if (x != null) {
				hits++;
			} else {
				adds++;
				x = makeIndicatorVar(conjunct);
				indicatorVars.put(conjunct, x);
				SmtLibTerm imp = makeImp(x, conjunct);
				shim.makeAssertion(imp);
				if (debugShim != null) {
					debugShim.makeAssertion(imp);
				}
			}
			xs.add(x);
		}
		if (Configuration.timeSmt) {
			double useRate = oldSize == 0 ? 1 : hits / oldSize;
			double hitRate = hits / formula.size();
			Configuration.recordCsaCacheStats(solverId, hitRate, useRate, oldSize, adds);
		}
		if (debugShim != null) {
			String msg = "\nBEGIN SMT JOB #" + id + " (SMT solver #" + hashCode() + "):\n";
			msg += baos.toString();
			msg += "END SMT JOB #" + id;
			System.err.println(msg);
		}
		List<SolverVariable> onVars = new ArrayList<>();
		List<SolverVariable> offVars = new ArrayList<>();
		for (SolverVariable x : indicatorVars.values()) {
			if (xs.contains(x)) {
				onVars.add(x);
			} else {
				offVars.add(x);
			}
		}
		return new Pair<>(onVars, offVars);
	}

	private SmtLibTerm makeImp(SolverVariable x, SmtLibTerm assertion) {
		Term[] args = { x, assertion };
		return (SmtLibTerm) Constructors.make(BuiltInConstructorSymbol.SMT_IMP, args);
	}

	private SolverVariable makeIndicatorVar(SmtLibTerm assertion) {
		Term[] args = Terms.singletonArray(Terms.makeDummyTerm(nextVarId++));
		ParameterizedConstructorSymbol sym = GlobalSymbolManager
				.getParameterizedSymbol(BuiltInConstructorSymbolBase.SMT_VAR);
		sym = sym.copyWithNewArgs(Param.wildCard(), new Param(BuiltInTypes.bool, ParamKind.PRE_SMT_TYPE));
		return (SolverVariable) Constructors.make(sym, args);
	}

	@Override
	protected void cleanup() {
		if (indicatorVars.size() > Configuration.smtCacheSize) {
			clearCache();
		}
	}

}
