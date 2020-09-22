package edu.harvard.seas.pl.formulog.ast;

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


import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Util;

public class Var extends AbstractTerm implements Term {

	static final AtomicInteger cnt = new AtomicInteger();
	
	private final String name;
	
	protected Var(String name) {
		this.name = name;
	}
	
	public static Var fresh(String name) {
		return new Var(name);
	}
	
	public static Var fresh() {
		return new Var("$" + cnt.getAndIncrement());
	}
	
	public boolean isUnderscore() {
		return name.equals("_");
	}
	
	public String getName() {
		return name;
	}
	
	@Override
	public String toString() {
		return name;
	}

	@Override
	public <I, O> O accept(TermVisitor<I, O> v, I in) {
		return v.visit(this, in);
	}

	@Override
	public <I, O, E extends Throwable> O accept(TermVisitorExn<I, O, E> v, I in) throws E {
		return v.visit(this, in);
	}

	@Override
	public boolean isGround() {
		return false;
	}

	@Override
	public boolean containsUnevaluatedTerm() {
		return false;
	}

	@Override
	public Term applySubstitution(Substitution s) {
		if (s.containsKey(this)) {
			return s.get(this);
		}
		return this;
	}

	@Override
	public Term normalize(Substitution s) throws EvaluationException {
		if (!s.containsKey(this)) {
			throw new EvaluationException("No binding for " + this);
		}
		return s.get(this);
	}

	@Override
	public void varSet(Set<Var> acc) {
		acc.add(this);
	}

	@Override
	public void updateVarCounts(Map<Var, Integer> counts) {
		int n = Util.lookupOrCreate(counts, this, () -> 0);
		counts.put(this, n + 1);
	}

	private static final Var hole = new Var("??");
	
	public static Var makeHole() {
		return hole;
	}
	
}
