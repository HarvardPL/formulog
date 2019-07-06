package edu.harvard.seas.pl.formulog.ast;

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

import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.validating.Stratum;

public class RelationProperties {

	private final Symbol relSym;
	private boolean bottomUp;
	private boolean topDown;
	private Symbol aggFuncSym;
	private Term aggInit;
	private Stratum stratum;
	
	public RelationProperties(Symbol relSym) {
		this.relSym = relSym;
	}
	
	public RelationProperties(RelationProperties props) {
		this(props.relSym);
		bottomUp = props.bottomUp;
		topDown = props.topDown;
		aggFuncSym = props.aggFuncSym;
		aggInit = props.aggInit;
		stratum = props.stratum;
	}

	public Symbol getRelationSymbol() {
		return relSym;
	}
	
	public synchronized void bottomUp() {
		if (topDown) {
			throw new IllegalStateException("Relation " + relSym + " cannot be both top-down and bottom-up");
		}
		bottomUp = true;
	}
	
	public synchronized void topDown() {
		if (bottomUp) {
			throw new IllegalStateException("Relation " + relSym + " cannot be both top-down and bottom-up");
		}
		topDown = true;
	}
	
	public synchronized void aggregate(Symbol funcSym, Term unit) {
		this.aggFuncSym = funcSym;
		this.aggInit = unit;
	}
	
	public synchronized boolean isBottomUp() {
		return bottomUp;
	}
	
	public synchronized boolean isTopDown() {
		return topDown;
	}

	public synchronized boolean isAggregated() {
		return aggFuncSym != null;
	}
	
	public synchronized Symbol getAggFuncSymbol() {
		return aggFuncSym;
	}

	public synchronized Term getAggFuncInit() {
		return aggInit;
	}
	
	public synchronized void setStratum(Stratum stratum) {
		this.stratum = stratum;
	}
	
	public synchronized Stratum getStratum() {
		return stratum;
	}

}
