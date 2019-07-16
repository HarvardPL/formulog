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

import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Util;

public class Var implements Term {

	private static final Map<String, Var> memo = new ConcurrentHashMap<>();
	
	static final AtomicInteger cnt = new AtomicInteger();
	
	private final String name;
	private final boolean isAnonymous;
	
	protected Var(String name, boolean isAnonymous) {
		this.name = name;
		this.isAnonymous = isAnonymous;
	}
	
	public static Var get(String name) {
		return Util.lookupOrCreate(memo, name, () -> new Var(name, false));
	}
	
	public static Var getFresh(boolean isAnonymous) {
		return new Var("_%" + cnt.getAndIncrement(), isAnonymous);
	}
	
	public boolean isAnonymous() {
		return isAnonymous;
	}

	@Override
	public String toString() {
		return name;
	}

	@Override
	public <I, O> O visit(TermVisitor<I, O> v, I in) {
		return v.visit(this, in);
	}

	@Override
	public <I, O, E extends Throwable> O visit(TermVisitorExn<I, O, E> v, I in) throws E {
		return v.visit(this, in);
	}

	@Override
	public boolean isGround() {
		return false;
	}

	@Override
	public boolean containsFunctionCall() {
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
		assert s.containsKey(this);
		return s.get(this);
	}

	@Override
	public void varSet(Set<Var> acc) {
		acc.add(this);
	}
	
}
