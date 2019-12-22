package edu.harvard.seas.pl.formulog.symbols.parameterized;

import java.util.Iterator;
import java.util.List;

import edu.harvard.seas.pl.formulog.util.Pair;

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

public final class ParamUtil {

	private ParamUtil() {
		throw new AssertionError("impossible");
	}

	public static boolean containsParamVars(Iterable<ParamElt> params) {
		for (ParamElt param : params) {
			if (param.containsParamVars()) {
				return true;
			}
		}
		return false;
	}

	public static Pair<ParamElt, ParamSubKind> findMismatch(List<ParamElt> args, List<ParamSubKind> kinds) {
		assert args.size() == kinds.size();
		Iterator<ParamSubKind> kindIt = kinds.iterator();
		for (Iterator<ParamElt> argIt = args.iterator(); argIt.hasNext();) {
			ParamElt arg = argIt.next();
			ParamSubKind kind = kindIt.next();
			if (!arg.matchesParamSubKind(kind)) {
				return new Pair<>(arg, kind);
			}
		}
		return null;
	}
	
	public static boolean matchParamSubKind(List<ParamElt> args, ParamSubKind kind) {
		for (ParamElt arg : args) {
			if (!arg.matchesParamSubKind(kind)) {
				return false;
			}
		}
		return true;
	}

}
