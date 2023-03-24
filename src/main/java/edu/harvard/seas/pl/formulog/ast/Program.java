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

import java.util.Set;

import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

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
