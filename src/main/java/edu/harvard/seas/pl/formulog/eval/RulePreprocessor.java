package edu.harvard.seas.pl.formulog.eval;

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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.symbols.BuiltInPredicateSymbol;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ValidProgram;

public class RulePreprocessor {

	public Set<BasicRule> preprocess(Rule r, ValidProgram prog) {
		List<Integer> idbIdxs = new ArrayList<>();
		int i = 0;
		for (Atom a : r.getBody()) {
			if (a.getSymbol().getSymbolType().isIDBSymbol() && !a.isNegated()) {
				idbIdxs.add(i);
			}
			++i;
		}
		List<Atom> head = Util.iterableToList(r.getHead());
		List<Atom> body = Util.iterableToList(r.getBody());
		if (idbIdxs.isEmpty()) {
			List<Atom> newBody = new ArrayList<>(body);
			sort(newBody);
			return Collections.singleton(BasicRule.get(head, newBody));
		}
		Set<BasicRule> rules = new HashSet<>();
		for (int idbIdx : idbIdxs) {
			List<Atom> newBody = new ArrayList<>(body);
			Atom first = newBody.remove(idbIdx);
			if (!(first instanceof UnifyAtom)) {
				/*
				 * We need to check if the first atom contains a reducible term (i.e., one that
				 * contains a function call). If it does, we replace that term with a variable
				 * and then unify the variable with the reducible term. E.g., p(f(X), Y) becomes
				 * p(Z, Y), Z = f(X). Otherwise what we want to be the first atom will get moved
				 * during sorting.
				 */
				Term[] args = first.getArgs();
				Term[] newArgs = new Term[args.length];
				for (int j = 0; j < args.length; ++j) {
					Term arg = args[j];
					if (arg.containsFunctionCall()) {
						Term var = Var.getFresh();
						newBody.add(0, Atoms.getPositive(BuiltInPredicateSymbol.UNIFY, new Term[] { var, arg }));
						newArgs[j] = var;
					} else {
						newArgs[j] = arg;
					}
				}
				first = Atoms.get(first.getSymbol(), newArgs, first.isNegated());
			}
			newBody.add(0, first);
			sort(newBody);
			rules.add(BasicRule.get(head, newBody));
		}
		return rules;
	}

	private void sort(List<Atom> body) {
		try {
			Set<Var> boundVars = new HashSet<>();
			for (int i = 0; i < body.size(); ++i) {
				for (int j = i; j < body.size(); ++j) {
					if (Unification.canBindVars(body.get(j), boundVars)) {
						boundVars.addAll(Atoms.varSet(body.get(j)));
						Collections.swap(body, i, j);
						break;
					}
				}
			}
		} catch (InvalidProgramException e) {
			throw new AssertionError();
		}
	}
	
}
