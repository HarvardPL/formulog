package formulog.ast;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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



import java.util.Set;

import formulog.functions.FunctionDef;
import formulog.symbols.ConstructorSymbol;
import formulog.symbols.FunctionSymbol;
import formulog.symbols.RelationSymbol;
import formulog.symbols.SymbolManager;
import formulog.symbols.TypeSymbol;

public interface Program<Q extends Literal, R extends Rule<Q, ?>> {

	Set<FunctionSymbol> getFunctionSymbols();
	
	Set<RelationSymbol> getFactSymbols();
	
	Set<RelationSymbol> getRuleSymbols();
	
	FunctionDef getDef(FunctionSymbol sym);
	
	Set<Term[]> getFacts(RelationSymbol sym);

	Set<R> getRules(RelationSymbol sym);
	
	SymbolManager getSymbolManager();
	
	boolean hasQuery();
	
	Q getQuery();
	
	FunctionCallFactory getFunctionCallFactory();
	
	Set<ConstructorSymbol> getUninterpretedFunctionSymbols();
	
	Set<TypeSymbol> getTypeSymbols();

}
