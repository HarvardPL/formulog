//package edu.harvard.seas.pl.formulog.symbols;
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
//public enum SymbolType {
//	
//	VANILLA_CONSTRUCTOR,
//	
//	INDEX_CONSTRUCTOR,
//	
//	TUPLE,
//	
//	SOLVER_VARIABLE,
//	
//	SOLVER_UNINTERPRETED_FUNCTION,
//
//	SOLVER_EXPR,
//	
//	SOLVER_CONSTRUCTOR_GETTER,
//	
//	SOLVER_CONSTRUCTOR_TESTER,
//	
//	FUNCTION,
//	
//	EDB_REL,
//	
//	IDB_REL,
//	
//	SPECIAL_REL,
//	
//	TYPE,
//	
//	TYPE_ALIAS,
//	
//	SOLVER_UNINTERPRETED_SORT,
//	
//	;
//	
//	public boolean isRelationSym() {
//		switch (this) {
//		case EDB_REL:
//		case IDB_REL:
//		case SPECIAL_REL:
//			return true;
//		default:
//			return false;
//		}
//	}
//	
//	public boolean isTypeSymbol() {
//		switch (this) {
//		case TYPE:
//		case SOLVER_UNINTERPRETED_SORT:
//			return true;
//		case TYPE_ALIAS:
//		case EDB_REL:
//		case FUNCTION:
//		case IDB_REL:
//		case SOLVER_UNINTERPRETED_FUNCTION:
//		case SOLVER_VARIABLE:
//		case SOLVER_EXPR:
//		case SOLVER_CONSTRUCTOR_GETTER:
//		case SOLVER_CONSTRUCTOR_TESTER:
//		case SPECIAL_REL:
//		case TUPLE:
//		case VANILLA_CONSTRUCTOR:
//		case INDEX_CONSTRUCTOR:
//			return false;
//		}
//		throw new AssertionError("impossible");
//	}
//	
//	public boolean isTypeOrTypeAliasSymbol() {
//		return isTypeSymbol() || this.equals(TYPE_ALIAS);
//	}
//	
//	public boolean isEDBSymbol() {
//		return this.equals(EDB_REL); 
//	}
//	
//	public boolean isIDBSymbol() {
//		return this.equals(IDB_REL);
//	}
//	
//	public boolean isFunctionSymbol() {
//		switch (this) {
//		case FUNCTION:
//			return true;
//		case EDB_REL:
//		case IDB_REL:
//		case SOLVER_UNINTERPRETED_FUNCTION:
//		case SOLVER_VARIABLE:
//		case SOLVER_EXPR:
//		case SOLVER_CONSTRUCTOR_GETTER:
//		case SOLVER_CONSTRUCTOR_TESTER:
//		case SPECIAL_REL:
//		case TUPLE:
//		case TYPE:
//		case TYPE_ALIAS:
//		case SOLVER_UNINTERPRETED_SORT:
//		case VANILLA_CONSTRUCTOR:
//		case INDEX_CONSTRUCTOR:
//			return false;
//		}
//		throw new AssertionError("impossible");
//	}
//	
//	public boolean isConstructorSymbol() {
//		switch (this) {
//		case EDB_REL:
//		case FUNCTION:
//		case IDB_REL:
//		case SPECIAL_REL:
//		case TYPE:
//		case TYPE_ALIAS:
//		case SOLVER_UNINTERPRETED_SORT:
//			return false;
//		case SOLVER_UNINTERPRETED_FUNCTION:
//		case SOLVER_VARIABLE:
//		case TUPLE:
//		case VANILLA_CONSTRUCTOR:
//		case SOLVER_EXPR:
//		case SOLVER_CONSTRUCTOR_GETTER:
//		case SOLVER_CONSTRUCTOR_TESTER:
//		case INDEX_CONSTRUCTOR:
//			return true;
//		}
//		throw new AssertionError("impossible");
//	}
//	
//	public boolean isSolverConstructorSymbol() {
//		switch (this) {
//		case SOLVER_UNINTERPRETED_FUNCTION:
//		case SOLVER_VARIABLE:
//		case SOLVER_EXPR:
//		case SOLVER_CONSTRUCTOR_GETTER:
//		case SOLVER_CONSTRUCTOR_TESTER:
//			return true;
//		case EDB_REL:
//		case FUNCTION:
//		case IDB_REL:
//		case SPECIAL_REL:
//		case TUPLE:
//		case TYPE:
//		case TYPE_ALIAS:
//		case SOLVER_UNINTERPRETED_SORT:
//		case VANILLA_CONSTRUCTOR:
//		case INDEX_CONSTRUCTOR:
//			return false;
//		}
//		throw new AssertionError("impossible");
//	}
//	
//}
