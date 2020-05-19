package edu.harvard.seas.pl.formulog.smt;

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

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import edu.harvard.seas.pl.formulog.util.Util;

public class BoolectorProcessFactory implements ExternalSolverProcessFactory {

	private static BoolectorProcessFactory instance;

	private BoolectorProcessFactory() {
		Util.assertBinaryOnPath("boolector");
	}

	public static BoolectorProcessFactory get() {
		if (instance == null) {
			synchronized (BoolectorProcessFactory.class) {
				if (instance == null) {
					instance = new BoolectorProcessFactory();
				}
			}
		}
		return instance;
	}

	@Override
	public Process newProcess(boolean incremental) throws IOException {
		List<String> command = new ArrayList<>();
		command.add("boolector");
		command.add("--smt2");
		if (incremental) {
			command.add("--incremental");
		}
		return new ProcessBuilder(command).redirectErrorStream(true).start();
	}
}
