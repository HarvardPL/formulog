package edu.harvard.seas.pl.formulog.symbols;

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

import edu.harvard.seas.pl.formulog.ast.Term;

public interface RelationSymbol extends TypedSymbol {

	boolean isIdbSymbol();

	default boolean isEdbSymbol() {
		return !isIdbSymbol();
	}

	void setAggregate(FunctionSymbol funcSym, Term unit);
	
	boolean setBottomUp();
	
	boolean setTopDown();

	boolean isAggregated();

	FunctionSymbol getAggFuncSym();
	
	Term getAggFuncUnit();
	
}
