package edu.harvard.seas.pl.formulog;

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

import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.util.Util;

public final class Configuration {

	private Configuration() {
		throw new AssertionError("impossible");
	}

	public static final boolean recordFuncDiagnostics = propIsSet("timeFuncs");
	private static final Map<FunctionSymbol, AtomicLong> funcTimes = new ConcurrentHashMap<>();
	
	static {
		if (recordFuncDiagnostics) {
			Runtime.getRuntime().addShutdownHook(new Thread() {
			
				@Override
				public void run() {
					printFuncDiagnostics(System.err);
				}
				
			});
		}
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
		int end = Math.min(times.size(), 20);
		for (int i = 0; i < end; ++i) {
			Map.Entry<FunctionSymbol, AtomicLong> e = it.next();
			out.println("[PERFORMANCE] " + e.getKey() + ": " + e.getValue().get() + "ms");
		}
	}

	private static final Comparator<Map.Entry<FunctionSymbol, AtomicLong>> sortTimes = new Comparator<Map.Entry<FunctionSymbol, AtomicLong>>() {

		@Override
		public int compare(Entry<FunctionSymbol, AtomicLong> e1, Entry<FunctionSymbol, AtomicLong> e2) {
			return -Long.compare(e1.getValue().get(), e2.getValue().get());
		}

	};

	private static boolean propIsSet(String prop) {
		String val = System.getProperty(prop);
		return val != null;
	}

}
