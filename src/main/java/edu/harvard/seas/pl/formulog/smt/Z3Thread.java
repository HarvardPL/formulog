package edu.harvard.seas.pl.formulog.smt;

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

import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinWorkerThread;

import edu.harvard.seas.pl.formulog.symbols.SymbolManager;

public class Z3Thread extends ForkJoinWorkerThread {

	private final Z3Process z3;

	protected Z3Thread(ForkJoinPool pool, SymbolManager symbolManager) {
		super(pool);
		z3 = new Z3Process(symbolManager);
	}

	@Override
	protected void onStart() {
		z3.start();
	}

	@Override
	protected void onTermination(Throwable exception) {
		z3.destroy();
	}

	public Z3Process getZ3Process() {
		return z3;
	}

}
