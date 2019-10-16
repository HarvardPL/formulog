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

import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.eval.EvaluationException;

public class CountingFJPImpl implements CountingFJP {

	private final ForkJoinPool exec;
	private final AtomicInteger taskCount = new AtomicInteger();
	private volatile EvaluationException failureCause;

	public CountingFJPImpl(int parallelism) {
		this.exec = new ForkJoinPool(parallelism, ForkJoinPool.defaultForkJoinWorkerThreadFactory,
				new Thread.UncaughtExceptionHandler() {

					@Override
					public void uncaughtException(Thread t, Throwable e) {
						System.err.println(e);
					}

				}, false);
	}

	public void externallyAddTask(AbstractFJPTask w) {
		taskCount.incrementAndGet();
		try {
			exec.execute(w);
		} catch (RejectedExecutionException e) {

		}
	}

	public void recursivelyAddTask(AbstractFJPTask w) {
		taskCount.incrementAndGet();
		w.fork();
	}

	public void reportTaskCompletion() {
		if (taskCount.decrementAndGet() == 0) {
			synchronized (taskCount) {
				taskCount.notify();
			}
		}
	}

	public final void blockUntilFinished() {
		synchronized (taskCount) {
			while (taskCount.get() > 0 && !hasFailed()) {
				try {
					taskCount.wait();
				} catch (InterruptedException e) {
					// do nothing
				}
			}
		}
	}

	public final void shutdown() {
		exec.shutdown();
		while (!exec.isTerminated()) {
			try {
				exec.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
			} catch (InterruptedException e) {
				// do nothing
			}
		}
	}

	public final void fail(EvaluationException cause) {
		failureCause = cause;
		exec.shutdownNow();
		synchronized (taskCount) {
			taskCount.notify();
		}
	}

	public final boolean hasFailed() {
		return failureCause != null;
	}

	public final EvaluationException getFailureCause() {
		return failureCause;
	}

}
