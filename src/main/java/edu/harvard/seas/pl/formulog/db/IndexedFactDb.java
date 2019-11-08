package edu.harvard.seas.pl.formulog.db;

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

import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public interface IndexedFactDb {

	Set<RelationSymbol> getSymbols();
	
	Iterable<Term[]> getAll(RelationSymbol sym);
	
	boolean isEmpty(RelationSymbol sym);
	
	int countDistinct(RelationSymbol sym);
	
	int numIndices(RelationSymbol sym);
	
	int countDuplicates(RelationSymbol sym);
	
	Iterable<Term[]> get(RelationSymbol sym, Term[] key, int index);
	
	boolean add(RelationSymbol sym, Term[] args);
	
	boolean addAll(RelationSymbol sym, Iterable<Term[]> tups);
	
	boolean hasFact(RelationSymbol sym, Term[] args);

	void clear();

}
