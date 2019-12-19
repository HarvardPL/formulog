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
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Util;

public class FP32 extends AbstractTerm implements Primitive<Float>, SmtLibTerm {

	private static final Map<Float, FP32> memo = new ConcurrentHashMap<>();
	private final float val;

	private FP32(float val) {
		this.val = val;
	}
	
	public static FP32 make(float val) {
		return Util.lookupOrCreate(memo, val, () -> new FP32(val));
	}

	@Override
	public Float getVal() {
		return val;
	}
	
	@Override
	public String toString() {
		if (Float.isNaN(val)) {
			return "fp32_nan";
		}
		if (val == Float.POSITIVE_INFINITY) {
			return "fp32_pos_infinity";
		}
		if (val == Float.NEGATIVE_INFINITY) {
			return "fp32_neg_infinity";
		}
		return Float.toString(val) + "F";
	}


	@Override
	public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
		return this;
	}
	
	@Override
	public void toSmtLib(SmtLibShim shim) {
		if (Float.isNaN(val)) {
			shim.print("(_ NaN 8 24)");
		} else if (val == Float.POSITIVE_INFINITY) {
			shim.print("(_ +oo 8 24)");
		} else if (val == Float.NEGATIVE_INFINITY) {
			shim.print("(_ -oo 8 24)");
		} else {
			shim.print("((_ to_fp 8 24) RNE " + val + ")");
		}
	}

	@Override
	public Type getType() {
		return BuiltInTypes.fp32;
	}
	
	@Override
	public Set<SolverVariable> freeVars() {
		return Collections.emptySet();
	}

}
