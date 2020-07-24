package edu.harvard.seas.pl.formulog.codegen;

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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;

import edu.harvard.seas.pl.formulog.Configuration;

public class CompileSh {

	public void print(File outDir) throws IOException {
		File dest = outDir.toPath().resolve("compile.sh").toFile();
		try (InputStream is = getClass().getClassLoader().getResourceAsStream("compile.sh");
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				PrintWriter out = new PrintWriter(dest)) {
			Worker w = new Worker(out);
			CodeGenUtil.copyOver(br, out, 0);
			w.defineVariables();
			CodeGenUtil.copyOver(br, out, -1);
			out.flush();
		}
		dest.setExecutable(true);
	}

	private class Worker {

		private final PrintWriter out;

		public Worker(PrintWriter out) {
			this.out = out;
		}

		void defineVariables() {
			String execName = Configuration.outputExec;
			if (execName == null) {
				execName = "flg";
			}
			defineVar("OUTPUT_EXEC", execName);
			if (Configuration.souffleInclude != null) {
				defineVar("SOUFFLE_INCLUDE", Configuration.souffleInclude);
			}
			if (Configuration.boostInclude != null) {
				defineVar("BOOST_INCLUDE", Configuration.boostInclude);
			}
			if (Configuration.boostLib != null) {
				defineVar("BOOST_LIB", "'" + Configuration.boostLib + "'");
			}
		}

		void defineVar(String var, String val) {
			out.println(var + "=" + val);
		}

	}

}
