package edu.harvard.seas.pl.formulog.ast;

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

import java.util.Arrays;

import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.FunctorUtil;

public abstract class PreFunctor<S extends Symbol> implements Functor<S> {

	private final S sym;
	private final Term[] args;
	
	protected PreFunctor(S sym, Term[] args) {
		this.sym = sym;
		this.args = args;
	}

	@Override
	public boolean isGround() {
		for (Term arg : args) {
			if (!arg.isGround()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public Term applySubstitution(Substitution s) {
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].applySubstitution(s);
		}
		return copyWithNewArgs(newArgs);
	}

	@Override
	public Term normalize(Substitution s) throws EvaluationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public int getId() {
		throw new UnsupportedOperationException();
	}

	@Override
	public S getSymbol() {
		return sym;
	}

	@Override
	public Term[] getArgs() {
		return args;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(args);
		result = prime * result + ((sym == null) ? 0 : sym.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		@SuppressWarnings("rawtypes")
		PreFunctor other = (PreFunctor) obj;
		if (!Arrays.equals(args, other.args))
			return false;
		if (sym == null) {
			if (other.sym != null)
				return false;
		} else if (!sym.equals(other.sym))
			return false;
		return true;
	}
	
	@Override
	public String toString() {
		return FunctorUtil.toString(sym, args);
	}

}
