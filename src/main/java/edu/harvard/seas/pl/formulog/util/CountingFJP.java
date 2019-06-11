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
import java.util.concurrent.ForkJoinPool.ForkJoinWorkerThreadFactory;
import java.util.concurrent.RecursiveAction;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

public class CountingFJP<T> {

	private final ForkJoinPool exec;
	private final AtomicInteger taskCount = new AtomicInteger();
	private volatile T failureCause;

	public CountingFJP(int parallelism, ForkJoinWorkerThreadFactory threadFactory) {
		this.exec = new ForkJoinPool(parallelism, threadFactory, new Thread.UncaughtExceptionHandler() {
			
			@Override
			public void uncaughtException(Thread t, Throwable e) {
				System.err.println(e);
			}
			
		}, false);
	}

	public void externallyAddTask(AbstractFJPTask<T> w) {
		taskCount.incrementAndGet();
		try {
			exec.execute(w);
		} catch (RejectedExecutionException e) {
			
		}
	}

	public void recursivelyAddTask(AbstractFJPTask<T> w) {
		taskCount.incrementAndGet();
		w.fork();
	}

	private void decrementTaskCount() {
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
	
	public final void fail(T cause) {
		failureCause = cause;
		exec.shutdownNow();
		synchronized (taskCount) {
			taskCount.notify();
		}
	}
	
	public final boolean hasFailed() {
		return failureCause != null;
	}
	
	public final T getFailureCause() {
		return failureCause;
	}

	@SuppressWarnings("serial")
	public static abstract class AbstractFJPTask<T> extends RecursiveAction {

		private final CountingFJP<T> exec;

		protected AbstractFJPTask(CountingFJP<T> exec) {
			this.exec = exec;
		}

		@Override
		protected void compute() {
			doTask();
			exec.decrementTaskCount();
		}

		public abstract void doTask();

	}

}
