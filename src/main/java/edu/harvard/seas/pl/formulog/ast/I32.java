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

import java.util.Collections;


import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.pcollections.PMap;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class I32 extends AbstractTerm implements Primitive<Integer>, SmtLibTerm {

	private static final Map<Integer, I32> memo = new ConcurrentHashMap<>();
	private final int val;
	
	private I32(int val) {
		this.val = val;
	}
	
	public static I32 make(int val) {
		return Util.lookupOrCreate(memo, val, () -> new I32(val));
	}

	@Override
	public Integer getVal() {
		return val;
	}
	
	@Override
	public String toString() {
		return Integer.toString(val);
	}

	@Override
	public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
		return this;
	}
	
	@Override
	public void toSmtLib(SmtLibShim shim) {
		shim.print("#x" + String.format("%08x", val));
	}

	@Override
	public Type getType() {
		return BuiltInTypes.i32;
	}
	
	@Override
	public Set<SolverVariable> freeVars() {
		return Collections.emptySet();
	}

}

