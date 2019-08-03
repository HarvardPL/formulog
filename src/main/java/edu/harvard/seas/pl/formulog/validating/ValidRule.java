package edu.harvard.seas.pl.formulog.validating;

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

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;

import edu.harvard.seas.pl.formulog.ast.AbstractRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;

public class ValidRule extends AbstractRule<UserPredicate, ComplexLiteral> {

	public static ValidRule make(Rule<UserPredicate, ComplexLiteral> rule, BiFunction<ComplexLiteral, Set<Var>, Integer> score)
			throws InvalidProgramException {
		try {
			List<ComplexLiteral> body = Util.iterableToList(rule);
			Set<Var> vars = new HashSet<>();
			order(body, score, vars);
			UserPredicate head = rule.getHead();
			if (!head.getSymbol().isIdbSymbol()) {
				throw new InvalidProgramException("Cannot create a rule for non-IDB symbol " + head.getSymbol());
			}
			if (!vars.containsAll(head.varSet())) {
				String msg = "There are unbound variables in the head of a rule:";
				for (Var x : head.varSet()) {
					if (!vars.contains(x)) {
						msg += " " + x;
					}
				}
				throw new InvalidProgramException(msg);
			}
			return new ValidRule(head, body);
		} catch (InvalidProgramException e) {
			throw new InvalidProgramException(e.getMessage() + "\n" + rule);
		}
	}

	public static void order(List<ComplexLiteral> atoms, BiFunction<ComplexLiteral, Set<Var>, Integer> score,
			Set<Var> boundVars) throws InvalidProgramException {
		for (int i = 0; i < atoms.size(); ++i) {
			int bestScore = Integer.MIN_VALUE;
			int bestPos = -1;
			for (int j = i; j < atoms.size(); ++j) {
				ComplexLiteral atom = atoms.get(j);
				if (Unification.canBindVars(atom, boundVars)) {
					int localScore = score.apply(atoms.get(j), boundVars);
					if (localScore > bestScore) {
						bestScore = localScore;
						bestPos = j;
					}
				}
			}
			if (bestPos == -1) {
				throw new InvalidProgramException("Literals do not admit an evaluable reordering");
			}
			Collections.swap(atoms, i, bestPos);
			boundVars.addAll(atoms.get(i).varSet());
		}
	}

	private ValidRule(UserPredicate head, List<ComplexLiteral> body) {
		super(head, body);
	}

}
