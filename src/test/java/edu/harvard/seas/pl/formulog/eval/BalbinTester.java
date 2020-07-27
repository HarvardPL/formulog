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


import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class BalbinTester extends AbstractTester<BalbinEvaluation> {

	public BalbinTester() { }

	@Override
	protected BalbinEvaluation setup(WellTypedProgram prog) throws InvalidProgramException {
		return BalbinEvaluation.setup(prog, 2);
	}

	@Override
	protected boolean evaluate(BalbinEvaluation eval) throws EvaluationException {
		eval.run();
		EvaluationResult res = eval.getResult();
		RelationSymbol sym;
		if (eval.hasQuery()) { // For now, BalbinEvaluation tests will always have a query
			sym = eval.getQuery().getSymbol();
		} else {
			sym = (RelationSymbol) eval.getInputProgram().getSymbolManager().lookupSymbol("ok");
		}
		return res.getAll(sym).iterator().hasNext();
	}

}
