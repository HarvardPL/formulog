package edu.harvard.seas.pl.formulog.eval.optimizations;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleRule;

public class SingleUseVarOptimizer {

	public SimpleRule optimize(SimpleRule rule) {
		Map<Var, Integer> counts = new HashMap<>();
		count(rule.getHead(), counts);
		for (SimpleLiteral l : rule) {
			count(l, counts);
		}
		Substitution s = new SimpleSubstitution();
		for (Map.Entry<Var, Integer> e : counts.entrySet()) {
			int n = e.getValue();
			if (n < 2) {
				s.put(e.getKey(), Var.getFresh(true));
			}
		}
		List<SimpleLiteral> newBody = new ArrayList<>();
		Set<Var> vars = new HashSet<>();
		for (SimpleLiteral l : rule) {
			if (l instanceof SimplePredicate) {
				SimplePredicate p = (SimplePredicate) l;
				Term[] newArgs = Terms.map(p.getArgs(), t -> t.applySubstitution(s));
				l = SimplePredicate.make(p.getSymbol(), newArgs, vars, p.isNegated());
			}
			newBody.add(l);
			vars.addAll(l.varSet());
		}
		return SimpleRule.make(rule.getHead(), newBody);
	}

	private void count(SimpleLiteral l, Map<Var, Integer> counts) {
		// This assumes that variables do not occur multiple times in a literal.
		// This should be safe. Only SimplePredicates are affected by this
		// optimization, and SimpleRules are constructed so that a
		// SimplePredicate never has duplicate variables as arguments.
		for (Var x : l.varSet()) {
			Integer n = counts.get(x);
			if (n == null) {
				n = 0;
			}
			counts.put(x, n + 1);
		}
	}
	
}
