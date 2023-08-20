package edu.harvard.seas.pl.formulog.util;

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

import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import java.util.ArrayDeque;
import java.util.Deque;

public class MockCountingFJP implements CountingFJP {

  private volatile EvaluationException failureCause;

  private final Deque<AbstractFJPTask> workItems = new ArrayDeque<>();

  public synchronized void externallyAddTask(AbstractFJPTask w) {
    workItems.addLast(w);
  }

  public synchronized void recursivelyAddTask(AbstractFJPTask w) {
    workItems.addLast(w);
  }

  public final synchronized void blockUntilFinished() {
    while (!workItems.isEmpty() && !hasFailed()) {
      AbstractFJPTask task = workItems.removeLast();
      task.compute();
    }
  }

  public final synchronized void shutdown() {}

  public final synchronized void fail(EvaluationException cause) {
    failureCause = cause;
  }

  public final synchronized boolean hasFailed() {
    return failureCause != null;
  }

  public final synchronized EvaluationException getFailureCause() {
    return failureCause;
  }

  @Override
  public synchronized void reportTaskCompletion() {}

  @Override
  public long getStealCount() {
    return 0;
  }
}
