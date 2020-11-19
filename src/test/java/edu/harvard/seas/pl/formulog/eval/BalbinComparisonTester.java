package edu.harvard.seas.pl.formulog.eval;

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


import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class BalbinComparisonTester extends AbstractTester<BalbinEvaluation> {

	public BalbinComparisonTester() { }

	@Override
	protected BalbinEvaluation setup(WellTypedProgram prog) throws InvalidProgramException {
		return BalbinEvaluation.setup(prog, 2);
	}

	protected SemiNaiveEvaluation setupSNE(WellTypedProgram prog) throws InvalidProgramException {
		return SemiNaiveEvaluation.setup(prog, 2, SemiNaiveEvaluation.EvalType.NORMAL);
	}

	protected boolean compare(BalbinEvaluation eval, EvaluationResult res, SemiNaiveEvaluation evalSNE, EvaluationResult resSNE) {
		// Add the BalbinEvaluation results to a set
		RelationSymbol sym = eval.getQuery().getSymbol();
		Iterator<UserPredicate> resIt = res.getAll(sym).iterator();
		Set<String> resSet = new HashSet<String>();
		while (resIt.hasNext()) {
			UserPredicate elt = resIt.next();
			resSet.add(elt.toString());
			System.out.println("BE elt: " + elt.toString());
		}

		// Add the SemiNaiveEvaluation results to a set
		RelationSymbol symSNE = evalSNE.getQuery().getSymbol();
		Iterator<UserPredicate> resItSNE = resSNE.getAll(symSNE).iterator();
		Set<String> resSetSNE = new HashSet<String>();
		while (resItSNE.hasNext()) {
			UserPredicate eltSNE = resItSNE.next();
			resSetSNE.add(eltSNE.toString());
			System.out.println("SNE elt: " + eltSNE.toString());
		}

		// Compare the evaluation results
		return resSet.equals(resSetSNE);
	}

	@Override
	protected boolean evaluate(BalbinEvaluation eval) throws EvaluationException, InvalidProgramException {
		eval.run();
		EvaluationResult res = eval.getResult();

		// Run SemiNaiveEvaluation on the input program
		WellTypedProgram prog = eval.getInputProgram();
		SemiNaiveEvaluation evalSNE = setupSNE(prog);
		evalSNE.run();
		EvaluationResult resSNE = evalSNE.getResult();

		return compare(eval, res, evalSNE, resSNE);
	}

}
