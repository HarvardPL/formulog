package edu.harvard.seas.pl.formulog.ast;

import java.util.Collections;

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

import org.pcollections.PMap;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.types.BuiltInTypesFactory;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class StringTerm extends AbstractTerm implements Primitive<String>, SmtLibTerm {

	private static final Map<String, StringTerm> memo = new ConcurrentHashMap<>();
	private final String val;
	
	private StringTerm(String val) {
		this.val = val;
	}
	
	public static StringTerm make(String val) {
		return Util.lookupOrCreate(memo, val, () -> new StringTerm(val));
	}

	@Override
	public String getVal() {
		return val;
	}
	
	@Override
	public String toString() {
		return "\"" + val + "\"";
	}

	@Override
	public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
		return this;
	}
	
	@Override
	public void toSmtLib(SmtLibShim shim) {
		String s = val.replace("\"", "\"\"");
		shim.print("\"" + s + "\"");
	}

	@Override
	public Type getType() {
		return BuiltInTypesFactory.string;
	}
	
	@Override
	public Set<SolverVariable> freeVars() {
		return Collections.emptySet();
	}

}
