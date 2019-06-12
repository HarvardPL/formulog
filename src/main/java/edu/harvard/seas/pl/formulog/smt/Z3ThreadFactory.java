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
import java.util.concurrent.ForkJoinPool.ForkJoinWorkerThreadFactory;
import java.util.concurrent.ForkJoinWorkerThread;

import edu.harvard.seas.pl.formulog.symbols.SymbolManager;

public class Z3ThreadFactory implements ForkJoinWorkerThreadFactory {

	private final SymbolManager symbolManager;

	public Z3ThreadFactory(SymbolManager symbolManager) {
		this.symbolManager = symbolManager;
	}

	@Override
	public ForkJoinWorkerThread newThread(ForkJoinPool pool) {
		return new Z3Thread(pool, symbolManager);
	}

}
