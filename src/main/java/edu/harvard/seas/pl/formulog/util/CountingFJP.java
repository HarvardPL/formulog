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

public interface CountingFJP {

	void externallyAddTask(AbstractFJPTask w);

	void recursivelyAddTask(AbstractFJPTask w);

	void reportTaskCompletion();

	void blockUntilFinished();

	default void blockUntilFinishedExn() throws EvaluationException {
		blockUntilFinished();
		if (hasFailed()) {
			throw getFailureCause();
		}
	}

	void shutdown();

	void fail(EvaluationException cause);

	boolean hasFailed();

	EvaluationException getFailureCause();

	long getStealCount();

}
