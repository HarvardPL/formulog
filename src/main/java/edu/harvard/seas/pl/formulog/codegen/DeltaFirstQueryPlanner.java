package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2023 President and Fellows of Harvard College
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
import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SAtom;
import edu.harvard.seas.pl.formulog.codegen.ast.souffle.SRule;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.validating.Stratum;

public class DeltaFirstQueryPlanner implements QueryPlanner {

	private final CodeGenContext ctx;

	public DeltaFirstQueryPlanner(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	@Override
	public List<Pair<Integer, int[]>> genPlan(SRule r, Stratum stratum) {
		List<Pair<Integer, int[]>> l = new ArrayList<>();
		var p = findDeltas(r, stratum);
		var numAtoms = p.fst();
		int i = 0;
		for (var deltaPos : p.snd()) {
			l.add(new Pair<>(i++, genPlanForDelta(deltaPos, numAtoms)));
		}
		return l;
	}

	private Pair<Integer, List<Integer>> findDeltas(SRule r, Stratum stratum) {
		List<Integer> l = new ArrayList<>();
		var body = r.getBody();
		var preds = stratum.getPredicateSyms();
		int numAtoms = 0;
		for (int i = 0; i < body.size(); ++i) {
			var lit = body.get(i);
			if (lit instanceof SAtom) {
			    numAtoms++;
				var pred = ((SAtom) lit).getSymbol();
				var rel = ctx.lookupRel(pred);
				if (rel != null && preds.contains(rel)) {
					l.add(i + 1);
				}
			}
		}
		return new Pair<>(numAtoms, l);
	}
	
	private int[] genPlanForDelta(int delta, int numAtoms) {
		int[] arr = new int[numAtoms];
		Arrays.setAll(arr, (i) -> {
			if (i == 0) {
				return delta;
			} else if (i < delta) {
				return i;
			} else {
				return i + 1;
			}
		});
		return arr;
	}

}
