//package edu.harvard.seas.pl.formulog.symbols.parameterized;
//
//import java.util.ArrayList;
//import java.util.List;
//
//import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
//import edu.harvard.seas.pl.formulog.util.TodoException;
//
///*-
// * #%L
// * FormuLog
// * %%
// * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
// * %%
// * Licensed under the Apache License, Version 2.0 (the "License");
// * you may not use this file except in compliance with the License.
// * You may obtain a copy of the License at
// * 
// *      http://www.apache.org/licenses/LICENSE-2.0
// * 
// * Unless required by applicable law or agreed to in writing, software
// * distributed under the License is distributed on an "AS IS" BASIS,
// * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// * See the License for the specific language governing permissions and
// * limitations under the License.
// * #L%
// */
//
//public final class ParamUtil {
//
//	private ParamUtil() {
//		throw new AssertionError("impossible");
//	}
//
//	public static List<ParamElt> instantiate(Iterable<ParamKind> kinds) {
//		List<ParamElt> params = new ArrayList<>();
//		for (ParamKind kind : kinds) {
//			switch (kind) {
//			case NAT:
//				params.add(new NatParam(TypeVar.fresh()));
//			case ANY_TYPE:
//				break;
//			case MODEL_FREE_TYPE:
//				break;
//			case PRE_SMT_TYPE:
//				break;
//			case SMT_VAR:
//				break;
//			case SMT_VARS:
//				break;
//			}
//		}
//		return params;
//	}
//
//}
