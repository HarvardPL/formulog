package edu.harvard.seas.pl.formulog;

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

import java.io.PrintStream;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.util.Util;

public final class Configuration {

	private Configuration() {
		throw new AssertionError("impossible");
	}

	public static final boolean recordFuncDiagnostics = propIsSet("timeFuncs");
	private static final Map<FunctionSymbol, AtomicLong> funcTimes = new ConcurrentHashMap<>();

	public static final boolean recordRuleDiagnostics = propIsSet("timeRules");
	private static final Map<Rule<?, ?>, AtomicLong> ruleTimes = new ConcurrentHashMap<>();

	public static final boolean noResults = propIsSet("noResults");

	public static final int optimizationSetting;

	public static final int minTaskSize;

	static {
		if (recordFuncDiagnostics) {
			Runtime.getRuntime().addShutdownHook(new Thread() {

				@Override
				public void run() {
					printFuncDiagnostics(System.err);
				}

			});
		}
		if (recordRuleDiagnostics) {
			Runtime.getRuntime().addShutdownHook(new Thread() {

				@Override
				public void run() {
					printRuleDiagnostics(System.err);
				}

			});
		}
		optimizationSetting = getIntProp("optimize", 0);
		minTaskSize = getIntProp("minTaskSize", 1024);
	}

	public static void recordFuncTime(FunctionSymbol func, long time) {
		AtomicLong l = Util.lookupOrCreate(funcTimes, func, () -> new AtomicLong());
		l.addAndGet(time);
	}

	public static Map<FunctionSymbol, AtomicLong> getFuncDiagnostics() {
		return Collections.unmodifiableMap(funcTimes);
	}

	public static void printFuncDiagnostics(PrintStream out) {
		Map<FunctionSymbol, AtomicLong> times = Configuration.getFuncDiagnostics();
		List<Map.Entry<FunctionSymbol, AtomicLong>> sorted = times.entrySet().stream().sorted(sortTimes)
				.collect(Collectors.toList());
		Iterator<Map.Entry<FunctionSymbol, AtomicLong>> it = sorted.iterator();
		int end = Math.min(times.size(), 10);
		for (int i = 0; i < end; ++i) {
			Map.Entry<FunctionSymbol, AtomicLong> e = it.next();
			out.println("[FUNC DIAGNOSTICS] " + e.getValue().get() + "ms: " + e.getKey());
		}
	}

	private static final Comparator<Map.Entry<?, AtomicLong>> sortTimes = new Comparator<Map.Entry<?, AtomicLong>>() {

		@Override
		public int compare(Entry<?, AtomicLong> e1, Entry<?, AtomicLong> e2) {
			return -Long.compare(e1.getValue().get(), e2.getValue().get());
		}

	};

	public static void recordRuleTime(Rule<?, ?> rule, long time) {
		AtomicLong l = Util.lookupOrCreate(ruleTimes, rule, () -> new AtomicLong());
		l.addAndGet(time);
	}

	public static Map<Rule<?, ?>, AtomicLong> getRuleDiagnostics() {
		return Collections.unmodifiableMap(ruleTimes);
	}

	public static void printRuleDiagnostics(PrintStream out) {
		Map<Rule<?, ?>, AtomicLong> times = Configuration.getRuleDiagnostics();
		List<Map.Entry<Rule<?, ?>, AtomicLong>> sorted = times.entrySet().stream().sorted(sortTimes)
				.collect(Collectors.toList());
		Iterator<Map.Entry<Rule<?, ?>, AtomicLong>> it = sorted.iterator();
		int end = Math.min(times.size(), 10);
		for (int i = 0; i < end; ++i) {
			Map.Entry<Rule<?, ?>, AtomicLong> e = it.next();
			out.println("[RULE DIAGNOSTICS] " + e.getValue().get() + "ms:\n" + e.getKey());
		}
	}

	private static boolean propIsSet(String prop) {
		String val = System.getProperty(prop);
		if (val == null) {
			return false;
		}
		if (!val.equals("")) {
			throw new IllegalArgumentException("Property " + prop + " does not take an argument");
		}
		return val != null;
	}

	private static int getIntProp(String prop, int def) {
		String val = System.getProperty(prop);
		if (val == null) {
			return def;
		}
		try {
			return Integer.parseInt(val);
		} catch (NumberFormatException e) {
			throw new IllegalArgumentException("Property " + prop + " expects an integer argument");
		}
	}

}
