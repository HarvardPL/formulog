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
import java.util.Set;

import org.pcollections.PMap;

import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public class BoolTerm extends AbstractTerm implements Primitive<Boolean>, SmtLibTerm {

	private final boolean val;
	private static final BoolTerm true_ = new BoolTerm(true);
	private static final BoolTerm false_ = new BoolTerm(false);
	
	private BoolTerm(boolean val) {
		this.val = val;
	}
	
	public static BoolTerm mk(boolean val) {
		return val ? true_ : false_;
	}
	
	public static BoolTerm mkTrue() {
		return true_;
	}
	
	public static BoolTerm mkFalse() {
		return false_;
	}

	@Override
	public Boolean getVal() {
		return val;
	}

	@Override
	public Type getType() {
		return BuiltInTypes.bool;
	}

	@Override
	public void toSmtLib(SmtLibShim shim) {
		shim.print(this.toString());
	}

	@Override
	public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
		return this;
	}

	@Override
	public Set<SolverVariable> freeVars() {
		return Collections.emptySet();
	}
	
	@Override
	public String toString() {
		return Boolean.toString(val);
	}

}
