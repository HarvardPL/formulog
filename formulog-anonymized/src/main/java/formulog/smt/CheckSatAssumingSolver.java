package formulog.smt;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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



import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import formulog.Configuration;
import formulog.ast.Constructors;
import formulog.ast.SmtLibTerm;
import formulog.ast.Term;
import formulog.ast.Terms;
import formulog.ast.Constructors.SolverVariable;
import formulog.eval.EvaluationException;
import formulog.symbols.BuiltInConstructorSymbol;
import formulog.symbols.GlobalSymbolManager;
import formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import formulog.symbols.parameterized.Param;
import formulog.symbols.parameterized.ParamKind;
import formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import formulog.types.BuiltInTypes;
import formulog.util.Pair;

public class CheckSatAssumingSolver extends AbstractSmtLibSolver {

	private final Map<SmtLibTerm, SolverVariable> indicatorVars = new HashMap<>();
	private int nextVarId;

	private void clearCache() throws EvaluationException {
		if (Configuration.timeSmt) {
			Configuration.recordCsaCacheClear(solverId);
		}
		indicatorVars.clear();
		nextVarId = 0;
		shim.reset();
		start();
	}

	public Set<SmtLibTerm> getCache() {
		return indicatorVars.keySet();
	}

	@Override
	protected Pair<List<SolverVariable>, List<SolverVariable>> makeAssertions(Collection<SmtLibTerm> formula)
			throws EvaluationException {
		int oldSize = indicatorVars.size();
		int hits = 0;
		int misses = 0;
		Set<SolverVariable> xs = new HashSet<>();
		for (SmtLibTerm conjunct : formula) {
			SolverVariable x = indicatorVars.get(conjunct);
			if (x != null) {
				hits++;
			} else {
				misses++;
				x = makeIndicatorVar(conjunct);
				indicatorVars.put(conjunct, x);
				SmtLibTerm imp = makeImp(x, conjunct);
				shim.makeAssertion(imp);
			}
			xs.add(x);
		}
		if (Configuration.timeSmt) {
			Configuration.recordCsaCacheStats(solverId, hits, misses, oldSize);
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
	protected void cleanup() throws EvaluationException {
		if (indicatorVars.size() > Configuration.smtCacheSize) {
			clearCache();
		}
	}

	@Override
	protected void start() throws EvaluationException {
		shim.setLogic(Configuration.smtLogic);
		shim.makeDeclarations();
	}

}
