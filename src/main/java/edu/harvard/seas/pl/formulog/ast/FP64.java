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

public class FP64 extends AbstractTerm implements Primitive<Double>, SmtLibTerm {

	private static final Map<Double, FP64> memo = new ConcurrentHashMap<>();
	private final double val;

	private FP64(double val) {
		this.val = val;
	}

	public static FP64 make(double val) {
		return Util.lookupOrCreate(memo, val, () -> new FP64(val));
	}

	@Override
	public Double getVal() {
		return val;
	}

	@Override
	public String toString() {
		if (Double.isNaN(val)) {
			return "fp64_nan";
		}
		if (val == Double.POSITIVE_INFINITY) {
			return "fp64_pos_infinity";
		}
		if (val == Double.NEGATIVE_INFINITY) {
			return "fp64_neg_infinity";
		}
		return Double.toString(val);
	}

	@Override
	public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
		return this;
	}

	@Override
	public void toSmtLib(SmtLibShim shim) {
		if (Double.isNaN(val)) {
			shim.print("(_ NaN 11 53)");
		} else if (val == Double.POSITIVE_INFINITY) {
			shim.print("(_ +oo 11 53)");
		} else if (val == Double.NEGATIVE_INFINITY) {
			shim.print("(_ -oo 11 53)");
		} else {
			shim.print("((_ to_fp 11 53) RNE " + val + ")");
		}
	}

	@Override
	public Type getType() {
		return BuiltInTypes.fp64;
	}

	@Override
	public Set<SolverVariable> freeVars() {
		return Collections.emptySet();
	}

}
