package edu.harvard.seas.pl.formulog.validating;

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

import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;

public class Stratum {

	private final int rank;
	private final Set<RelationSymbol> predicateSyms;
	private final boolean hasRecursiveNegationOrAggregation;

	public Stratum(int rank, Set<RelationSymbol> predicateSyms, boolean hasRecursiveNegationOrAggregation) {
		this.rank = rank;
		this.predicateSyms = predicateSyms;
		this.hasRecursiveNegationOrAggregation = hasRecursiveNegationOrAggregation;
	}

	public int getRank() {
		return rank;
	}
	
	public Set<RelationSymbol> getPredicateSyms() {
		return predicateSyms;
	}
	
	public boolean hasRecursiveNegationOrAggregation() {
		return hasRecursiveNegationOrAggregation;
	}

	@Override
	public String toString() {
		return "Stratum [rank=" + rank + ", predicateSyms=" + predicateSyms + ", hasRecursiveNegationOrAggregation="
				+ hasRecursiveNegationOrAggregation + "]";
	}	
	
}
