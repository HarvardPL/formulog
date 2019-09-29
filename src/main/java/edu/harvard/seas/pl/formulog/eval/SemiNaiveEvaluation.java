package edu.harvard.seas.pl.formulog.eval;

import java.time.LocalDateTime;
import java.util.ArrayDeque;

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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

import org.apache.commons.lang3.time.StopWatch;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.db.IndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb.SortedIndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.smt.Z3ThreadFactory;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.unification.OverwriteSubstitution;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.util.AbstractFJPTask;
import edu.harvard.seas.pl.formulog.util.CountingFJP;
import edu.harvard.seas.pl.formulog.util.CountingFJPImpl;
import edu.harvard.seas.pl.formulog.util.MockCountingFJP;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.FunctionDefValidation;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.BindingType;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleRule;

public class SemiNaiveEvaluation implements Evaluation {

	private final SortedIndexedFactDb db;
	private SortedIndexedFactDb deltaDb;
	private SortedIndexedFactDb nextDeltaDb;
	private final Map<RelationSymbol, Set<IndexedRule>> firstRoundRules = new HashMap<>();
	private final Map<RelationSymbol, Map<RelationSymbol, Set<IndexedRule>>> laterRoundRules = new HashMap<>();
	private final List<Stratum> strata;
	private final UserPredicate query;
	private volatile boolean changed;
	private final CountingFJP exec;
	private final Map<IndexedRule, boolean[]> splitPositions = new HashMap<>();

	private static final boolean sequential = System.getProperty("sequential") != null;
	private static final boolean debugRounds = Configuration.debugRounds;

	@SuppressWarnings("serial")
	public static SemiNaiveEvaluation setup(WellTypedProgram prog, int parallelism) throws InvalidProgramException {
		FunctionDefValidation.validate(prog);
		MagicSetTransformer mst = new MagicSetTransformer(prog);
		BasicProgram magicProg = mst.transform(Configuration.useDemandTransformation, true);

		Set<RelationSymbol> allRelations = new HashSet<>(magicProg.getFactSymbols());
		allRelations.addAll(magicProg.getRuleSymbols());
		SortedIndexedFactDbBuilder dbb = new SortedIndexedFactDbBuilder(allRelations);
		SortedIndexedFactDbBuilder deltaDbb = new SortedIndexedFactDbBuilder(magicProg.getRuleSymbols());
		IndexedFactDbWrapper wrappedDb = new IndexedFactDbWrapper();
		PredicateFunctionSetter predFuncs = new PredicateFunctionSetter(
				magicProg.getFunctionCallFactory().getDefManager(), magicProg.getSymbolManager(), wrappedDb);
		Map<RelationSymbol, Iterable<IndexedRule>> rules = new HashMap<>();
		List<Stratum> strata = new Stratifier(magicProg).stratify();
		for (Stratum stratum : strata) {
			if (stratum.hasRecursiveNegationOrAggregation()) {
				throw new InvalidProgramException("Cannot handle recursive negation or aggregation: " + stratum);
			}
			Set<RelationSymbol> stratumSymbols = stratum.getPredicateSyms();
			for (RelationSymbol sym : stratumSymbols) {
				List<IndexedRule> rs = new ArrayList<>();
				for (BasicRule br : magicProg.getRules(sym)) {
					for (SemiNaiveRule snr : SemiNaiveRule.make(br, stratumSymbols)) {
						BiFunction<ComplexLiteral, Set<Var>, Integer> score = chooseScoringFunction();
						ValidRule vr = ValidRule.make(snr, score);
						predFuncs.preprocess(vr);
						SimpleRule sr = SimpleRule.make(vr);
						IndexedRule ir = IndexedRule.make(sr, p -> {
							RelationSymbol psym = p.getSymbol();
							if (psym instanceof DeltaSymbol) {
								psym = ((DeltaSymbol) psym).getBaseSymbol();
								return deltaDbb.makeIndex(psym, p.getBindingPattern());
							} else {
								return dbb.makeIndex(psym, p.getBindingPattern());
							}
						});
						rs.add(ir);
					}
				}
				rules.put(sym, rs);
			}
		}
		SortedIndexedFactDb db = dbb.build();
		wrappedDb.set(db);

		CountingFJP exec;
		if (sequential) {
			exec = new MockCountingFJP();
		} else {
			exec = new CountingFJPImpl(parallelism, new Z3ThreadFactory(magicProg.getSymbolManager()));
		}

		for (RelationSymbol sym : magicProg.getFactSymbols()) {
			for (Iterable<Term[]> tups : Util.splitIterable(magicProg.getFacts(sym), taskSize)) {
				exec.externallyAddTask(new AbstractFJPTask(exec) {

					@Override
					public void doTask() throws EvaluationException {
						for (Term[] tup : tups) {
							try {
								db.add(sym, Terms.normalize(tup, new SimpleSubstitution()));
							} catch (EvaluationException e) {
								UserPredicate p = UserPredicate.make(sym, tup, false);
								throw new EvaluationException("Cannot normalize fact " + p + ":\n" + e.getMessage());
							}

						}
					}

				});
			}
		}
		exec.blockUntilFinished();
		if (exec.hasFailed()) {
			exec.shutdown();
			throw new InvalidProgramException(exec.getFailureCause());
		}
		// db.synchronize();
		return new SemiNaiveEvaluation(db, deltaDbb, rules, magicProg.getQuery(), strata, exec);
	}

	private static BiFunction<ComplexLiteral, Set<Var>, Integer> chooseScoringFunction() {
		switch (Configuration.optimizationSetting) {
		case 0:
			return SemiNaiveEvaluation::score0;
		case 1:
			return SemiNaiveEvaluation::score1;
		case 2:
			return SemiNaiveEvaluation::score2;
		default:
			throw new IllegalArgumentException(
					"Unrecognized optimization setting: " + Configuration.optimizationSetting);
		}
	}

	private static int score0(ComplexLiteral l, Set<Var> boundVars) {
		return 0;
	}

	private static int score1(ComplexLiteral l, Set<Var> boundVars) {
		// This seems to be worse than just doing nothing.
		return l.accept(new ComplexLiteralVisitor<Void, Integer>() {

			@Override
			public Integer visit(UnificationPredicate unificationPredicate, Void input) {
				return Integer.MAX_VALUE;
			}

			@Override
			public Integer visit(UserPredicate pred, Void input) {
				if (pred.isNegated()) {
					return Integer.MAX_VALUE;
				}
				if (pred.getSymbol() instanceof DeltaSymbol) {
					return 100;
				}
				Term[] args = pred.getArgs();
				if (args.length == 0) {
					return 150;
				}
				int bound = 0;
				for (int i = 0; i < args.length; ++i) {
					if (boundVars.containsAll(args[i].varSet())) {
						bound++;
					}
				}
				double percentBound = ((double) bound) / args.length * 100;
				return (int) percentBound;
			}

		}, null);
	}

	private static int score2(ComplexLiteral l, Set<Var> boundVars) {
		return l.accept(new ComplexLiteralVisitor<Void, Integer>() {

			@Override
			public Integer visit(UnificationPredicate unificationPredicate, Void input) {
				return Integer.MAX_VALUE;
			}

			@Override
			public Integer visit(UserPredicate pred, Void input) {
				Term[] args = pred.getArgs();
				if (args.length == 0) {
					return 150;
				}
				int bound = 0;
				for (int i = 0; i < args.length; ++i) {
					if (boundVars.containsAll(args[i].varSet())) {
						bound++;
					}
				}
				double percentBound = ((double) bound) / args.length * 100;
				return (int) percentBound;
			}

		}, null);
	}

	private SemiNaiveEvaluation(SortedIndexedFactDb db, IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb,
			Map<RelationSymbol, Iterable<IndexedRule>> rules, UserPredicate query, List<Stratum> strata,
			CountingFJP exec) {
		this.db = db;
		this.query = query;
		this.strata = strata;
		this.exec = exec;
		deltaDb = deltaDbb.build();
		nextDeltaDb = deltaDbb.build();
		processRules(rules);
	}

	private void processRules(Map<RelationSymbol, Iterable<IndexedRule>> rules) {
		SmtCallFinder scf = new SmtCallFinder();
		for (RelationSymbol sym : rules.keySet()) {
			Set<IndexedRule> firstRounders = new HashSet<>();
			Map<RelationSymbol, Set<IndexedRule>> laterRounders = new HashMap<>();
			for (IndexedRule rule : rules.get(sym)) {
				RelationSymbol delta = hasDelta(rule);
				if (delta != null) {
					Util.lookupOrCreate(laterRounders, delta, () -> new HashSet<>()).add(rule);
				} else {
					firstRounders.add(rule);
				}
				boolean[] positions = findSplitPositions(rule, scf);
				splitPositions.put(rule, positions);
//				System.err.println("[INDEXED RULE] " + rule);
			}
			firstRoundRules.put(sym, firstRounders);
			laterRoundRules.put(sym, laterRounders);
		}
	}

	private static boolean[] findSplitPositions(IndexedRule rule, SmtCallFinder scf) {
		int len = rule.getBodySize();
		boolean[] splitPositions = new boolean[len];
		boolean smtCallComing = scf.containsSmtCall(rule.getHead());
		for (int i = len - 1; i >= 0; --i) {
			SimpleLiteral l = rule.getBody(i);
			if (smtCallComing && l instanceof SimplePredicate && !((SimplePredicate) l).isNegated()) {
				splitPositions[i] = true;
				smtCallComing = scf.containsSmtCall(l);
			} else {
				smtCallComing = smtCallComing || scf.containsSmtCall(l);
			}
		}
		return splitPositions;
	}

	private RelationSymbol hasDelta(IndexedRule rule) {
		for (SimpleLiteral l : rule) {
			RelationSymbol delta = l.accept(new SimpleLiteralVisitor<Void, RelationSymbol>() {

				@Override
				public RelationSymbol visit(Assignment assignment, Void input) {
					return null;
				}

				@Override
				public RelationSymbol visit(Check check, Void input) {
					return null;
				}

				@Override
				public RelationSymbol visit(Destructor destructor, Void input) {
					return null;
				}

				@Override
				public RelationSymbol visit(SimplePredicate predicate, Void input) {
					if (predicate.getSymbol() instanceof DeltaSymbol) {
						return ((DeltaSymbol) predicate.getSymbol()).getBaseSymbol();
					} else {
						return null;
					}
				}

			}, null);
			if (delta != null) {
				return delta;
			}
		}
		return null;
	}

	@Override
	public synchronized void run() throws EvaluationException {
		if (Configuration.printRelSizes) {
			Runtime.getRuntime().addShutdownHook(new Thread() {

				@Override
				public void run() {
					Configuration.printRelSizes(System.err, "REL SIZE", db, true);
				}

			});
		}
		for (Stratum stratum : strata) {
			evaluateStratum(stratum);
		}
	}

	private void evaluateStratum(Stratum stratum) throws EvaluationException {
		int round = 0;
		StopWatch watch = recordRoundStart(stratum, round);
		Set<RelationSymbol> syms = stratum.getPredicateSyms();
		for (RelationSymbol sym : syms) {
			for (IndexedRule r : firstRoundRules.get(sym)) {
				exec.externallyAddTask(new RulePrefixEvaluator(r));
			}
		}
		exec.blockUntilFinished();
		if (exec.hasFailed()) {
			throw exec.getFailureCause();
		}
		recordRoundEnd(stratum, round, watch);
		updateDbs();
		while (changed) {
			round++;
			watch = recordRoundStart(stratum, round);
			changed = false;
			for (RelationSymbol sym : syms) {
				Map<RelationSymbol, Set<IndexedRule>> byDelta = laterRoundRules.get(sym);
				for (RelationSymbol delta : byDelta.keySet()) {
					if (!deltaDb.isEmpty(delta)) {
						for (IndexedRule r : byDelta.get(delta)) {
							exec.externallyAddTask(new RulePrefixEvaluator(r));
						}
					}
				}
			}
			exec.blockUntilFinished();
			if (exec.hasFailed()) {
				throw exec.getFailureCause();
			}
			recordRoundEnd(stratum, round, watch);
			updateDbs();
		}
	}

	@SuppressWarnings("serial")
	private void updateDbs() {
		StopWatch watch = recordDbUpdateStart();
		for (RelationSymbol sym : nextDeltaDb.getSymbols()) {
			if (nextDeltaDb.isEmpty(sym)) {
				continue;
			}
			Iterable<Term[]> answers = nextDeltaDb.getAll(sym);
			for (Iterable<Term[]> tups : Util.splitIterable(answers, taskSize)) {
				exec.externallyAddTask(new AbstractFJPTask(exec) {
			
					@Override
					public void doTask() {
						db.addAll(sym, tups);
					}
					
				});
			}
		}
		exec.blockUntilFinished();
		SortedIndexedFactDb tmp = deltaDb;
		deltaDb = nextDeltaDb;
		nextDeltaDb = tmp;
		nextDeltaDb.clear();
		recordDbUpdateEnd(watch);
	}

	private void reportFact(SimplePredicate atom) {
		RelationSymbol sym = atom.getSymbol();
		Term[] args = atom.getArgs();
		if (!db.hasFact(sym, args)) {
			nextDeltaDb.add(sym, args);
			changed = true;
		}
	}

	private static final int taskSize = Configuration.taskSize;
	private static final int smtTaskSize = Configuration.smtTaskSize;

	private Iterable<Iterable<Term[]>> lookup(IndexedRule r, int pos, OverwriteSubstitution s)
			throws EvaluationException {
		SimplePredicate predicate = (SimplePredicate) r.getBody(pos);
		int idx = r.getDBIndex(pos);
		Term[] args = predicate.getArgs();
		Term[] key = new Term[args.length];
		BindingType[] pat = predicate.getBindingPattern();
		for (int i = 0; i < args.length; ++i) {
			if (pat[i].isBound()) {
				key[i] = args[i].normalize(s);
			} else {
				key[i] = args[i];
			}
		}
		RelationSymbol sym = predicate.getSymbol();
		Iterable<Term[]> ans;
		if (sym instanceof DeltaSymbol) {
			ans = deltaDb.get(((DeltaSymbol) sym).getBaseSymbol(), key, idx);
		} else {
			ans = db.get(sym, key, idx);
		}
		boolean shouldSplit = splitPositions.get(r)[pos];
		int targetSize = shouldSplit ? smtTaskSize : taskSize;
		return Util.splitIterable(ans, targetSize);
	}

	private static final boolean recordRuleDiagnostics = Configuration.recordRuleDiagnostics;

	@SuppressWarnings("serial")
	private class RuleSuffixEvaluator extends AbstractFJPTask {

		private final IndexedRule rule;
		private final int startPos;
		private final OverwriteSubstitution s;
		private final Iterable<Term[]> tups;

		protected RuleSuffixEvaluator(IndexedRule rule, int pos, OverwriteSubstitution s, Iterable<Term[]> tups) {
			super(exec);
			this.rule = rule;
			this.startPos = pos;
			this.s = s;
			this.tups = tups;
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			try {
				for (Term[] tup : tups) {
					evaluate(tup);
				}
			} catch (UncheckedEvaluationException e) {
				throw new EvaluationException(e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRuleTime(rule, end - start);
			}
		}

		private void evaluate(Term[] ans) throws UncheckedEvaluationException {
			SimplePredicate p = (SimplePredicate) rule.getBody(startPos);
			updateBinding(p, ans);
			int pos = startPos + 1;
			Deque<Iterator<Term[]>> stack = new ArrayDeque<>();
			boolean movingRight = true;
			while (pos > startPos) {
				if (pos == rule.getBodySize()) {
					try {
						reportFact(rule.getHead().normalize(s));
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException("Exception raised while evaluating the literal: "
								+ rule.getHead() + "\n\n" + e.getMessage());
					}
					pos--;
					movingRight = false;
				} else if (movingRight) {
					SimpleLiteral l = rule.getBody(pos);
					try {
						switch (l.getTag()) {
						case ASSIGNMENT:
							((Assignment) l).assign(s);
							stack.addFirst(Collections.emptyIterator());
							pos++;
							break;
						case CHECK:
							if (((Check) l).check(s)) {
								stack.addFirst(Collections.emptyIterator());
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case DESTRUCTOR:
							if (((Destructor) l).destruct(s)) {
								stack.addFirst(Collections.emptyIterator());
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case PREDICATE:
							Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s).iterator();
							if (((SimplePredicate) l).isNegated()) {
								if (!tups.hasNext()) {
									stack.addFirst(Collections.emptyIterator());
									pos++;
								} else {
									pos--;
									movingRight = false;
								}
							} else {
								if (tups.hasNext()) {
									stack.addFirst(tups.next().iterator());
									while (tups.hasNext()) {
										exec.recursivelyAddTask(
												new RuleSuffixEvaluator(rule, pos, s.copy(), tups.next()));
									}
									// No need to do anything else: we'll hit the right case on the next iteration.
								} else {
									pos--;
								}
								movingRight = false;
							}
							break;
						}
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException(
								"Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
					}
				} else {
					Iterator<Term[]> it = stack.getFirst();
					if (it.hasNext()) {
						ans = it.next();
						updateBinding((SimplePredicate) rule.getBody(pos), ans);
						movingRight = true;
						pos++;
					} else {
						stack.removeFirst();
						pos--;
					}
				}
			}
		}

		private void updateBinding(SimplePredicate p, Term[] ans) {
			Term[] args = p.getArgs();
			BindingType[] pat = p.getBindingPattern();
			for (int i = 0; i < pat.length; ++i) {
				if (pat[i].isFree()) {
					s.put((Var) args[i], ans[i]);
				}
			}
		}

	}

	@SuppressWarnings("serial")
	private class RulePrefixEvaluator extends AbstractFJPTask {

		private final IndexedRule rule;

		protected RulePrefixEvaluator(IndexedRule rule) {
			super(exec);
			this.rule = rule;
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			try {
				int len = rule.getBodySize();
				int pos = 0;
				OverwriteSubstitution s = new OverwriteSubstitution();
				loop: for (; pos < len; ++pos) {
					SimpleLiteral l = rule.getBody(pos);
					try {
						switch (l.getTag()) {
						case ASSIGNMENT:
							((Assignment) l).assign(s);
							break;
						case CHECK:
							if (!((Check) l).check(s)) {
								return;
							}
							break;
						case DESTRUCTOR:
							if (!((Destructor) l).destruct(s)) {
								return;
							}
							break;
						case PREDICATE:
							SimplePredicate p = (SimplePredicate) l;
							if (p.isNegated()) {
								if (lookup(rule, pos, s).iterator().hasNext()) {
									return;
								}
							} else {
								// Stop on the first positive user predicate.
								break loop;
							}
							break;
						}
					} catch (EvaluationException e) {
						throw new EvaluationException(
								"Exception raised while evaluating the literal: " + l + "\n\n" + e.getMessage());
					}
				}
				if (pos == len) {
					try {
						reportFact(rule.getHead().normalize(s));
						return;
					} catch (EvaluationException e) {
						throw new EvaluationException("Exception raised while evaluationg the literal: "
								+ rule.getHead() + e.getLocalizedMessage());
					}
				}
				for (Iterable<Term[]> tups : lookup(rule, pos, s)) {
					exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, pos, s.copy(), tups));
				}
			} catch (EvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating this rule:\n" + rule + "\n\n" + e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRuleTime(rule, end - start);
			}
		}

	}

	@Override
	public synchronized EvaluationResult getResult() {
		return new EvaluationResult() {

			@Override
			public Iterable<UserPredicate> getAll(RelationSymbol sym) {
				if (!db.getSymbols().contains(sym)) {
					throw new IllegalArgumentException("Unrecognized relation symbol " + sym);
				}
				return new Iterable<UserPredicate>() {

					@Override
					public Iterator<UserPredicate> iterator() {
						return new FactIterator(sym, db.getAll(sym).iterator());
					}

				};
			}

			@Override
			public Iterable<UserPredicate> getQueryAnswer() {
				if (query == null) {
					return null;
				}
				RelationSymbol querySym = query.getSymbol();
				return new Iterable<UserPredicate>() {

					@Override
					public Iterator<UserPredicate> iterator() {
						return new FactIterator(querySym, db.getAll(querySym).iterator());
					}

				};
			}

			@Override
			public Set<RelationSymbol> getSymbols() {
				return Collections.unmodifiableSet(db.getSymbols());
			}

		};
	}

	private static class FactIterator implements Iterator<UserPredicate> {

		private final RelationSymbol sym;
		private final Iterator<Term[]> bindings;

		public FactIterator(RelationSymbol sym, Iterator<Term[]> bindings) {
			this.sym = sym;
			this.bindings = bindings;
		}

		@Override
		public boolean hasNext() {
			return bindings.hasNext();
		}

		@Override
		public UserPredicate next() {
			return UserPredicate.make(sym, bindings.next(), false);
		}

	}

	@Override
	public boolean hasQuery() {
		return query != null;
	}

	@Override
	public UserPredicate getQuery() {
		return query;
	}

	private static class IndexedFactDbWrapper implements IndexedFactDb {

		private IndexedFactDb db;

		public void set(IndexedFactDb db) {
			this.db = db;
		}

		@Override
		public Set<RelationSymbol> getSymbols() {
			return db.getSymbols();
		}

		@Override
		public Iterable<Term[]> getAll(RelationSymbol sym) {
			return db.getAll(sym);
		}

		@Override
		public Iterable<Term[]> get(RelationSymbol sym, Term[] key, int index) {
			return db.get(sym, key, index);
		}

		@Override
		public void add(RelationSymbol sym, Term[] args) {
			db.add(sym, args);
		}

		@Override
		public boolean hasFact(RelationSymbol sym, Term[] args) {
			return db.hasFact(sym, args);
		}

		@Override
		public void clear() {
			db.clear();
		}

		@Override
		public void addAll(RelationSymbol sym, Iterable<Term[]> tups) {
			db.addAll(sym, tups);
		}

		@Override
		public boolean isEmpty(RelationSymbol sym) {
			return db.isEmpty(sym);
		}

		@Override
		public int countDistinct(RelationSymbol sym) {
			return db.countDistinct(sym);
		}

		@Override
		public int numIndices(RelationSymbol sym) {
			return db.numIndices(sym);
		}

		@Override
		public int countDuplicates(RelationSymbol sym) {
			return db.countDuplicates(sym);
		}

	}
	

	private StopWatch recordRoundStart(Stratum stratum, int round) {
		if (!debugRounds) {
			return null;
		}
		System.err.println("#####");
		System.err.println("[START] Stratum " + stratum.getRank() + ", round " + round);
		LocalDateTime now = LocalDateTime.now();
		System.err.println("Start: " + now);
		StopWatch watch = new StopWatch();
		watch.start();
		return watch;
	}

	private void recordRoundEnd(Stratum stratum, int round, StopWatch watch) {
		if (watch == null) {
			return;
		}
		watch.stop();
		System.err.println("[END] Stratum " + stratum.getRank() + ", round " + round);
		System.err.println("Time: " + watch.getTime() + "ms");
	}
	

	private StopWatch recordDbUpdateStart() {
		if (!debugRounds) {
			return null;
		}
		System.err.println("[START] Updating DBs");
		LocalDateTime now = LocalDateTime.now();
		System.err.println("Start: " + now);
		StopWatch watch = new StopWatch();
		watch.start();
		return watch;
	}

	private void recordDbUpdateEnd(StopWatch watch) {
		if (watch == null) {
			return;
		}
		watch.stop();
		Configuration.printRelSizes(System.err, "DELTA SIZE", deltaDb, false);
		System.err.println("[END] Updating DBs");
		System.err.println("Time: " + watch.getTime() + "ms");
	}

}
