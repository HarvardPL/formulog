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


import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public abstract class AbstractStratumEvaluator implements StratumEvaluator {

	final Set<IndexedRule> noDeltaRules = new HashSet<>();
	final Map<RelationSymbol, Set<IndexedRule>> deltaRules = new HashMap<>();
	final Map<IndexedRule, boolean[]> splitPositions = new HashMap<>();
	
	public AbstractStratumEvaluator(Iterable<IndexedRule> rules) {
		processRules(rules);
	}
	
	private void processRules(Iterable<IndexedRule> rules) {
		SmtCallFinder scf = new SmtCallFinder();
		for (IndexedRule rule : rules) {
			RelationSymbol delta = EvalUtil.findDelta(rule);
			if (delta != null) {
				Util.lookupOrCreate(deltaRules, delta, () -> new HashSet<>()).add(rule);
			} else {
				noDeltaRules.add(rule);
			}
			boolean[] positions = findSplitPositions(rule, scf);
			splitPositions.put(rule, positions);
		}
	}

	private static boolean[] findSplitPositions(IndexedRule rule, SmtCallFinder scf) {
		int len = rule.getBodySize();
		boolean[] splitPositions = new boolean[len];
		boolean smtCallComing = scf.containsSmtCall(rule.getHead());
		for (int i = len - 1; i >= 0; --i) {
			SimpleLiteral l = rule.getBody(i);
			if (smtCallComing && l instanceof SimplePredicate && !((SimplePredicate) l).isNegated()) {
				splitPositions[i] = true;
				smtCallComing = scf.containsSmtCall(l);
			} else {
				smtCallComing = smtCallComing || scf.containsSmtCall(l);
			}
		}
		return splitPositions;
	}

}
