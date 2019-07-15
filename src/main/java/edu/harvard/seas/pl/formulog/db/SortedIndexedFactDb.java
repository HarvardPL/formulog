package edu.harvard.seas.pl.formulog.db;

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

import java.util.HashSet;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.Symbol;

public class SortedIndexedFactDb implements IndexedFactDB {

	@Override
	public Set<Symbol> getSymbols() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Term[]> getAll(Symbol sym) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<Term[]> get(Term[] key, int index) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public static class SortedIndexedFactDbBuilder implements IndexedFactDbBuilder<SortedIndexedFactDb> {

		private final Program prog;
		
		public SortedIndexedFactDbBuilder(Program prog) {
			this.prog = prog;
		}
		
		@Override
		public int makeIndex(NormalAtom atom, Set<Var> boundVars) {
			Term[] args = atom.getArgs();
			assert allUniqueVars(args);
			// TODO Auto-generated method stub
			return 0;
		}

		@Override
		public SortedIndexedFactDb build() {
			// TODO Auto-generated method stub
			return null;
		}
	
		private boolean allUniqueVars(Term[] args) {
			Set<Var> vars = new HashSet<>();
			for (Term t : args) {
				if (!(t instanceof Var) || !vars.add((Var) t)) {
					return false;
				}
			}
			return true;
		}
		
	}

}
