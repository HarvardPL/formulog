package edu.harvard.seas.pl.formulog.magic;

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
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public final class Adornments {

	private Adornments() {
		throw new AssertionError();
	}

	public static Atom adorn(Atom a, Set<Var> boundVars, Program prog, boolean topDownIsDefault) {
		Symbol origSym = a.getSymbol();
		if (!topDownIsDefault && !prog.getRelationProperties(origSym).isTopDown()) {
			return a;
		}
		boolean defaultAdornment = !prog.getRelationProperties(origSym).isBottomUp();
		Term[] args = a.getArgs();
		boolean[] adornment = new boolean[args.length];
		for (int k = 0; k < args.length; k++) {
			adornment[k] = defaultAdornment && boundVars.containsAll(Terms.varSet(args[k]));
		}
		AdornedSymbol sym = new AdornedSymbol(origSym, adornment);
		return Atoms.get(sym, args, a.isNegated());
	}

	public static Rule adornRule(Atom head, List<Atom> body, Program prog, boolean topDownIsDefault)
			throws InvalidProgramException {
		Symbol sym = head.getSymbol();
		boolean[] headAdornment;
		if (sym instanceof AdornedSymbol) {
			headAdornment = ((AdornedSymbol) head.getSymbol()).getAdornment();
		} else {
			headAdornment = new boolean[sym.getArity()];
			for (int i = 0; i < headAdornment.length; ++i) {
				headAdornment[i] = false;
			}
		}
		body = new ArrayList<>(body);
		Set<Var> boundVars = new HashSet<>();
		Term[] headArgs = head.getArgs();
		for (int i = 0; i < headArgs.length; i++) {
			if (headAdornment[i]) {
				boundVars.addAll(Terms.varSet(headArgs[i]));
			}
		}
		for (int i = 0; i < body.size(); i++) {
			boolean ok = false;
			for (int j = i; j < body.size(); j++) {
				Atom a = body.get(j);
				if (Unification.canBindVars(a, boundVars)) {
					Collections.swap(body, i, j);
					if (a.getSymbol().getSymbolType().isIDBSymbol()) {
						body.set(i, adorn((NormalAtom) a, boundVars, prog, topDownIsDefault));
					}
					boundVars.addAll(Atoms.varSet(a));
					ok = true;
					break;
				}
			}
			if (!ok) {
				throw new InvalidProgramException(
						"Cannot reorder rule to meet well-modeness restrictions: " + BasicRule.get(head, body));
			}
		}
		return BasicRule.get(head, body);
	}

}
