package edu.harvard.seas.pl.formulog.util;

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

public class MockCountingFJP<T> implements CountingFJP<T> {

	private volatile T failureCause;
	private volatile boolean shutdown;

	public synchronized void externallyAddTask(AbstractFJPTask<T> w) {
		assert !shutdown;
		w.compute();
	}

	public synchronized void recursivelyAddTask(AbstractFJPTask<T> w) {
		assert !shutdown;
		w.compute();
	}

	public synchronized final void blockUntilFinished() {
		
	}

	public synchronized final void shutdown() {
		assert !shutdown;
		shutdown = true;
	}
	
	public synchronized final void fail(T cause) {
		failureCause = cause;
		shutdown = true;
	}
	
	public synchronized final boolean hasFailed() {
		return failureCause != null;
	}
	
	public synchronized final T getFailureCause() {
		return failureCause;
	}

	@Override
	public synchronized void reportTaskCompletion() {
		assert !shutdown;
	}

}
