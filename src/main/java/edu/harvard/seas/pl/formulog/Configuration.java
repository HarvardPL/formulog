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

import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.eval.IndexedRule;
import edu.harvard.seas.pl.formulog.smt.*;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Dataset;
import edu.harvard.seas.pl.formulog.util.EnumerableThreadLocal;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.SharedLong;
import edu.harvard.seas.pl.formulog.util.Util;
import java.io.PrintStream;
import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public final class Configuration {

  private Configuration() {
    throw new AssertionError("impossible");
  }

  public static final boolean runTests = propIsSet("runTests");
  public static final String testFile = System.getProperty("testFile");

  public static final boolean recordFuncDiagnostics = propIsSet("timeFuncs");
  private static final Map<FunctionSymbol, AtomicLong> funcTimes = new ConcurrentHashMap<>();

  public static final boolean recordRuleDiagnostics = propIsSet("timeRules");
  private static final Map<Rule<?, ?>, Pair<AtomicLong, AtomicLong>> ruleTimes =
      new ConcurrentHashMap<>();

  public static final boolean debugSmt = propIsSet("debugSmt");
  public static final String debugSmtOutDir = getStringProp("debugSmtOutDir", "solver_logs");

  public static final boolean timeSmt = propIsSet("timeSmt");
  public static final boolean smtMemoize = propIsSet("smtMemoize", true);
  private static final Map<SmtLibSolver, Dataset> perProcessSmtEvalStats =
      new ConcurrentHashMap<>();
  private static final Dataset smtEvalStats = new Dataset();
  private static final AtomicLong smtDeclGlobalsTime = new AtomicLong();
  private static final AtomicLong smtEncodeTime = new AtomicLong();
  private static final AtomicLong smtDeclTime = new AtomicLong();
  private static final AtomicLong smtInferTime = new AtomicLong();
  private static final AtomicLong smtSerialTime = new AtomicLong();
  public static final SharedLong smtWaitTime = new SharedLong();
  private static final AtomicInteger smtNumCallsSat = new AtomicInteger();
  private static final AtomicInteger smtNumCallsUnsat = new AtomicInteger();
  private static final AtomicInteger smtNumCallsUnknown = new AtomicInteger();
  private static final AtomicInteger smtNumCallsDoubleCheck = new AtomicInteger();
  private static final AtomicInteger smtNumCallsFalseUnknown = new AtomicInteger();

  // XXX I don't think this is being used any more
  private static final AtomicLong smtTotalTime = new AtomicLong();

  public static void recordSmtTime(long delta) {
    smtTotalTime.addAndGet(delta);
  }

  public static long getSmtTotalTime() {
    return smtTotalTime.get();
  }

  public static final boolean printRelSizes = propIsSet("printRelSizes");
  public static final boolean printFinalRules = propIsSet("printFinalRules");
  public static final boolean simplifyFormulaVars = propIsSet("simplifyFormulaVars", true);
  public static final boolean debugRounds = propIsSet("debugRounds");
  public static final boolean debugParallelism = propIsSet("debugParallelism");

  public static final int optimizationSetting = getIntProp("optimize", 0);

  public static final int taskSize = getIntProp("taskSize", 128);

  public static final int smtTaskSize = getIntProp("smtTaskSize", 8);
  public static final int smtCacheSize = getIntProp("smtCacheSize", 100);
  public static final String smtSolver;

  static {
    smtSolver = getStringProp("smtSolver", "z3");
    switch (smtSolver) {
      case "z3":
      case "cvc4":
      case "yices":
      case "boolector":
        break;
      default:
        throw new IllegalArgumentException("Unrecognized solver: " + smtSolver);
    }
  }

  public static final String smtLogic = getStringProp("smtLogic", "ALL");
  public static final boolean smtDeclareAdts = propIsSet("smtDeclareAdts", true);
  public static final boolean smtCacheHardResets = propIsSet("smtCacheHardResets", false);
  public static final boolean smtUseNegativeLiterals = propIsSet("smtUseNegativeLiterals", false);
  public static final boolean smtDoubleCheckUnknowns = propIsSet("smtDoubleCheckUnknowns", true);
  public static final boolean smtUseSingleShotSolver =
      propIsSet("smtUseSingleShotSolver", false) || smtSolver.equals("boolector");
  public static final boolean smtCheckSuccess = propIsSet("smtCheckSuccess", false);

  private static final Dataset pushPopStackSize = new Dataset();
  private static final Dataset pushPopStackReuse = new Dataset();
  private static final Dataset pushPopStackPushes = new Dataset();
  private static final Dataset pushPopStackPops = new Dataset();
  private static final Dataset pushPopStackDelta = new Dataset();
  private static final Dataset csaCacheHitRate = new Dataset();
  private static final Dataset csaCacheUseRate = new Dataset();
  private static final Dataset csaCacheSize = new Dataset();
  private static final Dataset csaCacheHits = new Dataset();
  private static final Dataset csaCacheMisses = new Dataset();
  private static final AtomicInteger csaCacheClears = new AtomicInteger();
  private static final Dataset csaEvalStats = new Dataset();
  private static final Dataset pushPopEvalStats = new Dataset();
  private static final Dataset otherSolverEvalStats = new Dataset();

  public static final boolean oneRuleAtATime = propIsSet("oneRuleAtATime");
  public static final boolean parallelizeInnerLoops = propIsSet("parallelizeInnerLoops", true);

  public static final boolean useDemandTransformation = propIsSet("useDemandTransformation", true);
  public static final boolean restoreStratification = propIsSet("restoreStratification", true);

  public static final List<String> trackedRelations = getListProp("trackedRelations");

  public static final boolean debugMst = propIsSet("debugMst");
  public static final boolean debugStratification = propIsSet("debugStratification");
  public static final String debugStratificationOutDir =
      getStringProp("debugStratificationOutDir", "stratification_graphs");

  public static final boolean testCodegen = propIsSet("testCodegen");
  public static final boolean keepCodegenTestDirs = propIsSet("keepCodegenTestDirs");
  public static final String cxxCompiler = getStringProp("cxxCompiler", null);

  public static final String souffleInclude = System.getProperty("souffleInclude");
  public static final String boostInclude = System.getProperty("boostInclude");
  public static final String boostLib = System.getProperty("boostLib");
  public static final String tbbInclude = System.getProperty("tbbInclude");
  public static final String tbbLib = System.getProperty("tbbLib");
  public static final String outputExec = System.getProperty("outputExec");

  public static final int memoizeThreshold() {
    return getIntProp("memoizeThreshold", 0);
  }

  public static final boolean genComparators = propIsSet("genComparators", true);
  public static final boolean minIndex = propIsSet("minIndex", true);

  public static final boolean inlineInRules = propIsSet("inlineInRules", true);

  public static final boolean eagerSemiNaive = propIsSet("eagerSemiNaive");
  public static final boolean codegenSplitOnSmt = propIsSet("codegenSplitOnSmt");

  public static final boolean useHashDbFilter = propIsSet("useHashDbFilter");

  public static final boolean recordWork = propIsSet("recordWork");
  public static final boolean recordDetailedWork = propIsSet("recordDetailedWork");
  public static final SharedLong work = new SharedLong();
  public static final SharedLong workItems = new SharedLong();
  public static final SharedLong newDerivs = new SharedLong();
  public static final SharedLong dupDerivs = new SharedLong();
  public static final Map<IndexedRule, SharedLong> workPerRule = new ConcurrentHashMap<>();

  public static class SmtStats {
    public long time;
    public long ncalls;

    public void add(long time) {
      this.time += time;
      ncalls++;
    }
  }

  public static final EnumerableThreadLocal<SmtStats> smtTime =
      new EnumerableThreadLocal<>(SmtStats::new);
  public static final SharedLong smtCacheClears = new SharedLong();
  public static final SharedLong smtCacheHits = new SharedLong();
  public static final SharedLong smtCacheMisses = new SharedLong();

  static {
    if (recordFuncDiagnostics) {
      Runtime.getRuntime()
          .addShutdownHook(
              new Thread() {

                @Override
                public void run() {
                  printFuncDiagnostics(System.err);
                }
              });
    }
    if (recordRuleDiagnostics) {
      Runtime.getRuntime()
          .addShutdownHook(
              new Thread() {

                @Override
                public void run() {
                  printRuleDiagnostics(System.err);
                }
              });
    }
    if (timeSmt) {
      Runtime.getRuntime()
          .addShutdownHook(
              new Thread() {

                @Override
                public void run() {
                  printSmtDiagnostics(System.err);
                }
              });
    }
    Runtime.getRuntime()
        .addShutdownHook(
            new Thread() {

              @Override
              public void run() {
                printConfiguration(System.err);
              }
            });
  }

  public static synchronized void printConfiguration(PrintStream out) {
    // out.println("[CONFIG] noResults=" + noResults);
    // out.println("[CONFIG] timeRules=" + recordRuleDiagnostics);
    // out.println("[CONFIG] timeFuncs=" + recordFuncDiagnostics);
    // out.println("[CONFIG] timeSmt=" + timeSmt);
    // out.println("[CONFIG] optimize=" + optimizationSetting);
    // out.println("[CONFIG] taskSize=" + taskSize);
    // out.println("[CONFIG] smtTaskSize=" + smtTaskSize);
    // out.println("[CONFIG] memoizeThreshold=" + memoizeThreshold());
    // out.println("[CONFIG] noModel=" + noModel());
  }

  public static void recordSmtDeclTime(long time) {
    smtDeclTime.addAndGet(time);
  }

  public static void recordSmtInferTime(long time) {
    smtInferTime.addAndGet(time);
  }

  public static void recordSmtSerialTime(long time) {
    smtSerialTime.addAndGet(time);
  }

  public static void recordSmtEvalTime(
      SmtLibSolver solver, long encodeTime, long evalTime, SmtStatus result) {
    smtEncodeTime.addAndGet(encodeTime);
    smtEvalStats.addDataPoint(evalTime);
    if (solver instanceof CheckSatAssumingSolver) {
      csaEvalStats.addDataPoint(evalTime);
    } else if (solver instanceof PushPopSolver) {
      pushPopEvalStats.addDataPoint(evalTime);
    } else {
      otherSolverEvalStats.addDataPoint(evalTime);
    }
    Util.lookupOrCreate(perProcessSmtEvalStats, solver, () -> new Dataset()).addDataPoint(evalTime);
    switch (result) {
      case SATISFIABLE:
        smtNumCallsSat.incrementAndGet();
        break;
      case UNKNOWN:
        smtNumCallsUnknown.incrementAndGet();
        break;
      case UNSATISFIABLE:
        smtNumCallsUnsat.incrementAndGet();
        break;
    }
  }

  public static void recordSmtWaitTime(long time) {
    smtWaitTime.add(time);
  }

  public static void recordSmtDeclGlobalsTime(long time) {
    smtDeclGlobalsTime.addAndGet(time);
  }

  public static synchronized void printSmtDiagnostics(PrintStream out) {
    Dataset callsPerSolver = new Dataset();
    Dataset timePerSolver = new Dataset();
    for (Dataset ds : perProcessSmtEvalStats.values()) {
      callsPerSolver.addDataPoint(ds.size());
      timePerSolver.addDataPoint(ds.computeSum());
    }
    out.println("[SMT WAIT TIME] " + smtWaitTime.unsafeGet() / 1e6 + "ms");
    out.println("[SMT DECL GLOBALS TIME] " + smtDeclGlobalsTime.get() / 1e6 + "ms");
    out.println("[SMT ENCODE TIME - TOTAL] " + smtEncodeTime.get() / 1e6 + "ms");
    out.println("[SMT ENCODE TIME - DECL] " + smtDeclTime.get() / 1e6 + "ms");
    out.println("[SMT ENCODE TIME - INFER] " + smtInferTime.get() / 1e6 + "ms");
    out.println("[SMT ENCODE TIME - SERIAL] " + smtSerialTime.get() / 1e6 + "ms");
    out.printf("[SMT EVAL TIME] %1.1fms%n", smtEvalStats.computeSum() / 1e6);
    out.println("[SMT EVAL TIME PER CALL (ms)] " + smtEvalStats.getStatsString(1e-6));
    out.println("[SMT EVAL TIME PER SOLVER (ms)] " + timePerSolver.getStatsString(1e-6));
    out.println("[SMT NUM CALLS PER SOLVER] " + callsPerSolver.getStatsString());
    out.println("[SMT NUM CALLS - SAT] " + smtNumCallsSat);
    out.println("[SMT NUM CALLS - UNSAT] " + smtNumCallsUnsat);
    out.println("[SMT NUM CALLS - UNKNOWN] " + smtNumCallsUnknown);
    out.println("[SMT NUM CALLS - DOUBLE CHECK] " + smtNumCallsDoubleCheck);
    out.println("[SMT NUM CALLS - FALSE UNKNOWN] " + smtNumCallsFalseUnknown);
    if (csaEvalStats.size() > 0) {
      out.println("--- CSA ---");
      out.printf("[CSA EVAL TIME] %1.1fms%n", csaEvalStats.computeSum() / 1e6);
      out.println("[CSA EVAL TIME PER CALL (ms)] " + csaEvalStats.getStatsString(1e-6));
      out.println("[CSA CACHE LIMIT] " + smtCacheSize);
      out.println("[CSA CACHE BASE SIZE] " + csaCacheSize.getStatsString());
      out.println("[CSA CACHE HITS] " + csaCacheHits.getStatsString());
      out.println("[CSA CACHE MISSES] " + csaCacheMisses.getStatsString());
      out.println("[CSA CACHE HIT RATE] " + csaCacheHitRate.getStatsString());
      out.println("[CSA CACHE USE RATE] " + csaCacheUseRate.getStatsString());
      out.println("[CSA CACHE CLEARS] " + csaCacheClears.get());
    }
    if (pushPopEvalStats.size() > 0) {
      out.println("--- PUSH POP ---");
      out.printf("[PUSH POP EVAL TIME] %1.1fms%n", pushPopEvalStats.computeSum() / 1e6);
      out.println("[PUSH POP EVAL TIME PER CALL (ms)] " + pushPopEvalStats.getStatsString(1e-6));
      out.println("[PUSH POP STACK BASE SIZE] " + pushPopStackSize.getStatsString());
      out.println("[PUSH POP STACK PUSHES] " + pushPopStackPushes.getStatsString());
      out.println("[PUSH POP STACK POPS] " + pushPopStackPops.getStatsString());
      out.println("[PUSH POP STACK DELTA] " + pushPopStackDelta.getStatsString());
      out.println("[PUSH POP STACK REUSE] " + pushPopStackReuse.getStatsString());
    }
    if (otherSolverEvalStats.size() > 0) {
      out.println("--- OTHER ---");
      out.printf("[OTHER EVAL TIME] %1.1fms%n", otherSolverEvalStats.computeSum() / 1e6);
      out.println("[OTHER EVAL TIME PER CALL (ms)] " + otherSolverEvalStats.getStatsString(1e-6));
    }
  }

  public static void recordPushPopSolverStats(
      int solverId, int stackStartSize, int pops, int pushes) {
    pushPopStackSize.addDataPoint(stackStartSize);
    pushPopStackReuse.addDataPoint(stackStartSize - pops);
    pushPopStackPops.addDataPoint(pops);
    pushPopStackPushes.addDataPoint(pushes);
    pushPopStackDelta.addDataPoint(pushes - pops);
  }

  public static void recordCsaCacheStats(int solverId, int hits, int misses, int oldSize) {
    int numAsserts = hits + misses;
    csaCacheHits.addDataPoint(hits);
    csaCacheMisses.addDataPoint(misses);
    csaCacheHitRate.addDataPoint(numAsserts == 0 ? 1 : (double) hits / numAsserts);
    csaCacheUseRate.addDataPoint(oldSize == 0 ? 1 : (double) hits / oldSize);
    csaCacheSize.addDataPoint(oldSize);
  }

  public static void recordSmtDoubleCheck(boolean falseUnknown) {
    smtNumCallsDoubleCheck.incrementAndGet();
    if (falseUnknown) {
      smtNumCallsFalseUnknown.incrementAndGet();
    }
  }

  public static void recordCsaCacheClear(int solverId) {
    csaCacheClears.incrementAndGet();
  }

  public static void recordFuncTime(FunctionSymbol func, long time) {
    AtomicLong l = Util.lookupOrCreate(funcTimes, func, () -> new AtomicLong());
    l.addAndGet(time);
  }

  public static Map<FunctionSymbol, AtomicLong> getFuncDiagnostics() {
    return Collections.unmodifiableMap(funcTimes);
  }

  public static synchronized void printFuncDiagnostics(PrintStream out) {
    Map<FunctionSymbol, AtomicLong> times = Configuration.getFuncDiagnostics();
    List<Map.Entry<FunctionSymbol, AtomicLong>> sorted =
        times.entrySet().stream().sorted(sortTimes).collect(Collectors.toList());
    Iterator<Map.Entry<FunctionSymbol, AtomicLong>> it = sorted.iterator();
    int end = Math.min(times.size(), 10);
    for (int i = 0; i < end; ++i) {
      Map.Entry<FunctionSymbol, AtomicLong> e = it.next();
      out.println("[FUNC DIAGNOSTICS] " + e.getValue().get() + "ms: " + e.getKey());
    }
  }

  private static final Comparator<Map.Entry<?, AtomicLong>> sortTimes =
      new Comparator<Map.Entry<?, AtomicLong>>() {

        @Override
        public int compare(Entry<?, AtomicLong> e1, Entry<?, AtomicLong> e2) {
          return -Long.compare(e1.getValue().get(), e2.getValue().get());
        }
      };

  private static final Comparator<Map.Entry<?, Pair<AtomicLong, AtomicLong>>> sortPairedTimes =
      new Comparator<Map.Entry<?, Pair<AtomicLong, AtomicLong>>>() {

        @Override
        public int compare(
            Entry<?, Pair<AtomicLong, AtomicLong>> e1, Entry<?, Pair<AtomicLong, AtomicLong>> e2) {
          return -Long.compare(getTotal(e1), getTotal(e2));
        }

        private long getTotal(Entry<?, Pair<AtomicLong, AtomicLong>> e) {
          Pair<AtomicLong, AtomicLong> p = e.getValue();
          return p.fst().get() + p.snd().get();
        }
      };

  public static void recordRulePrefixTime(Rule<?, ?> rule, long time) {
    Pair<AtomicLong, AtomicLong> p =
        Util.lookupOrCreate(ruleTimes, rule, () -> new Pair<>(new AtomicLong(), new AtomicLong()));
    p.fst().addAndGet(time);
  }

  public static void recordRuleSuffixTime(Rule<?, ?> rule, long time) {
    Pair<AtomicLong, AtomicLong> p =
        Util.lookupOrCreate(ruleTimes, rule, () -> new Pair<>(new AtomicLong(), new AtomicLong()));
    p.snd().addAndGet(time);
  }

  public static synchronized void printRuleDiagnostics(PrintStream out) {
    Map<Rule<?, ?>, Pair<AtomicLong, AtomicLong>> times = ruleTimes;
    List<Map.Entry<Rule<?, ?>, Pair<AtomicLong, AtomicLong>>> sorted =
        times.entrySet().stream().sorted(sortPairedTimes).collect(Collectors.toList());
    Iterator<Map.Entry<Rule<?, ?>, Pair<AtomicLong, AtomicLong>>> it = sorted.iterator();
    int end = Math.min(times.size(), 10);
    for (int i = 0; i < end; ++i) {
      Map.Entry<Rule<?, ?>, Pair<AtomicLong, AtomicLong>> e = it.next();
      Pair<AtomicLong, AtomicLong> p = e.getValue();
      long pre = p.fst().get();
      long suf = p.snd().get();
      long total = pre + suf;
      out.println(
          "[RULE DIAGNOSTICS] " + total + " (" + pre + " + " + suf + ") ms:\n" + e.getKey());
    }
  }

  public static synchronized void printRelSizes(
      PrintStream out, String header, IndexedFactDb db, boolean printEmpty) {
    for (RelationSymbol sym : db.getSymbols()) {
      if (printEmpty || !db.isEmpty(sym)) {
        out.println(
            "["
                + header
                + "] "
                + sym
                + ": "
                + db.countDistinct(sym)
                + " / "
                + db.numIndices(sym)
                + " / "
                + db.countDuplicates(sym));
      }
    }
  }

  private static boolean propIsSet(String prop, boolean defaultValue) {
    String val = System.getProperty(prop);
    if (val == null) {
      return defaultValue;
    }
    if (val.equals("true") || val.equals("")) {
      return true;
    }
    if (val.equals("false")) {
      return false;
    }
    throw new IllegalArgumentException("Unexpected argument for property " + prop + ": " + val);
  }

  private static boolean propIsSet(String prop) {
    return propIsSet(prop, false);
  }

  static int getIntProp(String prop, int def) {
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

  private static String getStringProp(String prop, String def) {
    String val = System.getProperty(prop);
    if (val == null) {
      return def;
    }
    return val;
  }

  static List<String> getListProp(String prop) {
    String val = System.getProperty(prop);
    if (val == null || val.equals("")) {
      return Collections.emptyList();
    }
    List<String> l = new ArrayList<>();
    breakIntoCollection(val, l);
    return Collections.unmodifiableList(l);
  }

  private static void breakIntoCollection(String s, Collection<String> acc) {
    int split;
    while ((split = s.indexOf(',')) != -1) {
      String sub = s.substring(0, split);
      acc.add(sub);
      if (split == s.length()) {
        return;
      }
      s = s.substring(split + 1);
    }
    acc.add(s);
  }

  static SmtStrategy getSmtStrategy() {
    String val = System.getProperty("smtStrategy");
    if (val == null) {
      val = "queue-1";
    }

    switch (val) {
      case "naive":
        return new SmtStrategy(SmtStrategy.Tag.NAIVE, null);
      case "pushPop":
        return new SmtStrategy(SmtStrategy.Tag.PUSH_POP, null);
      case "pushPopNaive":
        return new SmtStrategy(SmtStrategy.Tag.PUSH_POP_NAIVE, null);
      case "perThreadNaive":
        return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_NAIVE, null);
      case "perThreadPushPop":
        return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_PUSH_POP, null);
      case "perThreadPushPopNaive":
        return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_PUSH_POP_NAIVE, null);
    }

    Pattern p = Pattern.compile("queue-(\\d+)");
    Matcher m = p.matcher(val);
    if (m.matches()) {
      int size = Integer.parseInt(m.group(1));
      return new SmtStrategy(SmtStrategy.Tag.QUEUE, size);
    }
    p = Pattern.compile("bestMatch-(\\d+)");
    m = p.matcher(val);
    if (m.matches()) {
      int size = Integer.parseInt(m.group(1));
      return new SmtStrategy(SmtStrategy.Tag.BEST_MATCH, size);
    }
    p = Pattern.compile("perThreadQueue-(\\d+)");
    m = p.matcher(val);
    if (m.matches()) {
      int size = Integer.parseInt(m.group(1));
      return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_QUEUE, size);
    }
    p = Pattern.compile("perThreadBestMatch-(\\d+)");
    m = p.matcher(val);
    if (m.matches()) {
      int size = Integer.parseInt(m.group(1));
      return new SmtStrategy(SmtStrategy.Tag.PER_THREAD_BEST_MATCH, size);
    }
    throw new IllegalArgumentException("Unrecognized SMT strategy: " + val);
  }
}
