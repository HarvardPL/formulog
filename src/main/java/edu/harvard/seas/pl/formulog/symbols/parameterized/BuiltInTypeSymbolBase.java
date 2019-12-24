//package edu.harvard.seas.pl.formulog.symbols.parameterized;
//
//import java.util.Arrays;
//import java.util.List;
//
//import edu.harvard.seas.pl.formulog.symbols.TypeSymbolType;
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
//public enum BuiltInTypeSymbolBase implements SymbolBase {
//	
//	BV("bv", ParamSubKind.NAT),
//
//	FP("fp", ParamSubKind.NAT, ParamSubKind.NAT),
//	
//	;
//	
//	private final String name;
//	private final List<ParamSubKind> paramTypes;
//
//	private BuiltInTypeSymbolBase(String name, ParamSubKind... params) {
//		this.name = name;
//		this.paramTypes = Arrays.asList(params);
//	}
//
//	@Override
//	public int getArity() {
//		return 0;
//	}
//
//	@Override
//	public List<ParamSubKind> getParamSubKinds() {
//		return paramTypes;
//	}
//
//	@Override
//	public String getName() {
//		return name;
//	}
//	
//	public TypeSymbolType getTypeSymbolType() {
//		return TypeSymbolType.NORMAL_TYPE;
//	}
//
//}
