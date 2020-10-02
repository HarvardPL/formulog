package edu.harvard.seas.pl.formulog;

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

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveEvaluation;
import edu.harvard.seas.pl.formulog.parsing.ParseException;
import edu.harvard.seas.pl.formulog.parsing.Parser;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.util.Dataset;

public final class Main {

	private final String file;

	private Main(String file) {
		this.file = file;
	}

	private void clearGlobalStats() {
		Configuration.smtEvalStats.clear();
		Configuration.csaCacheHits.clear();
		Configuration.pushPopStackReuse.clear();
		Configuration.stealCount = 0;
		Configuration.externalSubmissions = 0;
	}

	private void go() throws Exception {
		Program<UserPredicate, BasicRule> prog = parse();
		WellTypedProgram typedProg = new TypeChecker(prog).typeCheck();
		for (int i = 0; i < Configuration.numRuns; ++i) {
			typedProg.getFunctionCallFactory().clearCache();
			clearGlobalStats();
			SemiNaiveEvaluation eval = SemiNaiveEvaluation.setup(typedProg, Configuration.parallelism,
					Configuration.eagerSemiNaive);
			long start = System.currentTimeMillis();
			eval.run();
			printResults(i, System.currentTimeMillis() - start);
		}
	}

	private Dataset getSmtCacheReuseData() {
		switch (Configuration.smtStrategy.getTag()) {
		case NAIVE:
		case PER_THREAD_NAIVE:
			return new Dataset();
		case PER_THREAD_PUSH_POP:
		case PER_THREAD_PUSH_POP_NAIVE:
		case PUSH_POP:
		case PUSH_POP_NAIVE:
			return Configuration.pushPopStackReuse;
		case PER_THREAD_BEST_MATCH:
		case PER_THREAD_QUEUE:
		case BEST_MATCH:
		case QUEUE:
			return Configuration.csaCacheHits;
		}
		throw new AssertionError("impossible");
	}

	private void printResults(int run, long time) {
		System.out.print("formulog: run " + run + ": ");
		System.out.print(time);
		System.out.print("," + (long) (Configuration.smtEvalStats.computeSum() / 1e6));
		System.out.print("," + Configuration.smtEvalStats.size());
		Dataset smtCacheReuse = getSmtCacheReuseData();
		System.out.printf(",%.1f", smtCacheReuse.computeMean());
		System.out.printf(",%.1f", smtCacheReuse.computeMedian());
		System.out.print("," + (Configuration.stealCount - Configuration.externalSubmissions));
		System.out.println();
	}

	private Program<UserPredicate, BasicRule> parse() throws FileNotFoundException, ParseException {
		List<Path> factDirs = Configuration.factDirs.stream().map(Paths::get).collect(Collectors.toList());
		if (factDirs.isEmpty()) {
			factDirs = Collections.singletonList(Paths.get(""));
		}
		FileReader reader = new FileReader(file);
		Program<UserPredicate, BasicRule> prog = new Parser().parse(reader, factDirs);
		return prog;
	}

	public static void main(String[] args) throws Exception {
		if (args.length != 1) {
			throw new IllegalArgumentException("Excepted a single Formulog file as an argument.");
		}
		new Main(args[0]).go();
	}

}
