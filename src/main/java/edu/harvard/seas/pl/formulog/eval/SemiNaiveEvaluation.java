package edu.harvard.seas.pl.formulog.eval;

import java.time.LocalDateTime;

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
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.IndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb.SortedIndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.eval.SemiNaiveRule.DeltaSymbol;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.smt.BestMatchSmtManager;
import edu.harvard.seas.pl.formulog.smt.PerThreadSmtManager;
import edu.harvard.seas.pl.formulog.smt.QueueSmtManager;
import edu.harvard.seas.pl.formulog.smt.SmtManager;
import edu.harvard.seas.pl.formulog.smt.SmtStrategy;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
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
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleRule;

public class SemiNaiveEvaluation implements Evaluation {

	final SortedIndexedFactDb db;
	SortedIndexedFactDb deltaDb;
	SortedIndexedFactDb nextDeltaDb;
	final Map<RelationSymbol, Set<IndexedRule>> firstRoundRules = new HashMap<>();
	final Map<RelationSymbol, Map<RelationSymbol, Set<IndexedRule>>> laterRoundRules = new HashMap<>();
	final List<Stratum> strata;
	final UserPredicate query;
	volatile boolean changed;
	final CountingFJP exec;
	final Map<IndexedRule, boolean[]> splitPositions = new HashMap<>();
	final Set<RelationSymbol> trackedRelations;

	static final boolean sequential = System.getProperty("sequential") != null;
	static final boolean debugRounds = Configuration.debugRounds;

	@SuppressWarnings("serial")
	public static SemiNaiveEvaluation setup(WellTypedProgram prog, int parallelism) throws InvalidProgramException {
		FunctionDefValidation.validate(prog);
		MagicSetTransformer mst = new MagicSetTransformer(prog);
		BasicProgram magicProg = mst.transform(Configuration.useDemandTransformation, true);
		Set<RelationSymbol> allRelations = new HashSet<>(magicProg.getFactSymbols());
		allRelations.addAll(magicProg.getRuleSymbols());
		SortedIndexedFactDbBuilder dbb = new SortedIndexedFactDbBuilder(allRelations);
		SortedIndexedFactDbBuilder deltaDbb = new SortedIndexedFactDbBuilder(magicProg.getRuleSymbols());
		PredicateFunctionSetter predFuncs = new PredicateFunctionSetter(
				magicProg.getFunctionCallFactory().getDefManager(), magicProg.getSymbolManager(), dbb);

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
						if (Configuration.printFinalRules) {
							System.err.println("[FINAL RULE]:\n" + ir);
						}
					}
				}
				rules.put(sym, rs);
			}
		}
		SortedIndexedFactDb db = dbb.build();
		predFuncs.setDb(db);

		SmtManager smt = getSmtManager(magicProg);
		prog.getFunctionCallFactory().getDefManager().loadBuiltInFunctions(smt);

		CountingFJP exec;
		if (sequential) {
			exec = new MockCountingFJP();
		} else {
			exec = new CountingFJPImpl(parallelism);
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
		return new SemiNaiveEvaluation(db, deltaDbb, rules, magicProg.getQuery(), strata, exec,
				getTrackedRelations(magicProg.getSymbolManager()));
	}

	static SmtManager getSmtManager(Program<UserPredicate, BasicRule> prog) {
		SmtStrategy strategy = Configuration.smtStrategy;
		switch (strategy.getTag()) {
		case QUEUE: {
			int size = (int) strategy.getMetadata();
			return new QueueSmtManager(prog, size);
		}
		case BEST_MATCH: {
			int size = (int) strategy.getMetadata();
			return new BestMatchSmtManager(prog, size);
		}
		case PER_THREAD_QUEUE: {
			int size = (int) strategy.getMetadata();
			return new PerThreadSmtManager(() -> new QueueSmtManager(prog, size));
		}
		case PER_THREAD_BEST_MATCH: {
			int size = (int) strategy.getMetadata();
			return new PerThreadSmtManager(() -> new BestMatchSmtManager(prog, size));
		}
		default:
			throw new UnsupportedOperationException("Cannot support SMT strategy: " + strategy);
		}

	}

	static Set<RelationSymbol> getTrackedRelations(SymbolManager sm) {
		Set<RelationSymbol> s = new HashSet<>();
		for (String name : Configuration.trackedRelations) {
			if (sm.hasName(name)) {
				Symbol sym = sm.lookupSymbol(name);
				if (sym instanceof RelationSymbol) {
					s.add((RelationSymbol) sm.lookupSymbol(name));
				} else {
					System.err.println("[WARNING] Cannot track non-relation " + sym);
				}

			} else {
				System.err.println("[WARNING] Cannot track unrecognized relation " + name);
			}
		}
		return s;
	}

	static BiFunction<ComplexLiteral, Set<Var>, Integer> chooseScoringFunction() {
		switch (Configuration.optimizationSetting) {
		case 0:
			return SemiNaiveEvaluation::score0;
		case 1:
			return SemiNaiveEvaluation::score1;
		case 2:
			return SemiNaiveEvaluation::score2;
		case 3:
			return SemiNaiveEvaluation::score3;
		default:
			throw new IllegalArgumentException(
					"Unrecognized optimization setting: " + Configuration.optimizationSetting);
		}
	}

	static int score0(ComplexLiteral l, Set<Var> boundVars) {
		return 0;
	}

	static int score1(ComplexLiteral l, Set<Var> boundVars) {
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

	static int score2(ComplexLiteral l, Set<Var> boundVars) {
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

	static int score3(ComplexLiteral l, Set<Var> boundVars) {
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
					return 125;
				}
				Term[] args = pred.getArgs();
				if (args.length == 0) {
					return Integer.MAX_VALUE;
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

	SemiNaiveEvaluation(SortedIndexedFactDb db, IndexedFactDbBuilder<SortedIndexedFactDb> deltaDbb,
			Map<RelationSymbol, Iterable<IndexedRule>> rules, UserPredicate query, List<Stratum> strata,
			CountingFJP exec, Set<RelationSymbol> trackedRelations) {
		this.db = db;
		this.query = query;
		this.strata = strata;
		this.exec = exec;
		this.trackedRelations = trackedRelations;
		deltaDb = deltaDbb.build();
		nextDeltaDb = deltaDbb.build();
		processRules(rules);
	}

	void processRules(Map<RelationSymbol, Iterable<IndexedRule>> rules) {
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
				// System.err.println("[INDEXED RULE] " + rule);
			}
			firstRoundRules.put(sym, firstRounders);
			laterRoundRules.put(sym, laterRounders);
		}
	}

	static boolean[] findSplitPositions(IndexedRule rule, SmtCallFinder scf) {
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

	RelationSymbol hasDelta(IndexedRule rule) {
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

	void evaluateStratum(Stratum stratum) throws EvaluationException {
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

	void updateDbs() {
		StopWatch watch = recordDbUpdateStart();
		for (RelationSymbol sym : nextDeltaDb.getSymbols()) {
			if (nextDeltaDb.isEmpty(sym)) {
				continue;
			}
			Iterable<Iterable<Term[]>> answers = Util.splitIterable(nextDeltaDb.getAll(sym), taskSize);
			exec.externallyAddTask(new UpdateDbTask(sym, answers.iterator()));
		}
		exec.blockUntilFinished();
		SortedIndexedFactDb tmp = deltaDb;
		deltaDb = nextDeltaDb;
		nextDeltaDb = tmp;
		nextDeltaDb.clear();
		recordDbUpdateEnd(watch);
	}

	@SuppressWarnings("serial")
	class UpdateDbTask extends AbstractFJPTask {

		final RelationSymbol sym;
		final Iterator<Iterable<Term[]>> it;

		protected UpdateDbTask(RelationSymbol sym, Iterator<Iterable<Term[]>> it) {
			super(exec);
			this.sym = sym;
			this.it = it;
		}

		@Override
		public void doTask() throws EvaluationException {
			Iterable<Term[]> tups = it.next();
			if (it.hasNext()) {
				exec.recursivelyAddTask(new UpdateDbTask(sym, it));
			}
			db.addAll(sym, tups);
		}

	}

	void reportFact(SimplePredicate atom) {
		RelationSymbol sym = atom.getSymbol();
		Term[] args = atom.getArgs();
		if (!db.hasFact(sym, args) && nextDeltaDb.add(sym, args)) {
			changed = true;
			if (trackedRelations.contains(sym)) {
				System.err.println("[TRACKED] " + UserPredicate.make(sym, args, false));
			}
		}
	}

	static final int taskSize = Configuration.taskSize;
	static final int smtTaskSize = Configuration.smtTaskSize;

	Iterable<Iterable<Term[]>> lookup(IndexedRule r, int pos, OverwriteSubstitution s) throws EvaluationException {
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

	static final boolean recordRuleDiagnostics = Configuration.recordRuleDiagnostics;

	@SuppressWarnings("serial")
	class RuleSuffixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;
		final SimplePredicate head;
		final SimpleLiteral[] body;
		final int startPos;
		final OverwriteSubstitution s;
		final Iterator<Iterable<Term[]>> it;

		protected RuleSuffixEvaluator(IndexedRule rule, SimplePredicate head, SimpleLiteral[] body, int pos,
				OverwriteSubstitution s, Iterator<Iterable<Term[]>> it) {
			super(exec);
			this.rule = rule;
			this.head = head;
			this.body = body;
			this.startPos = pos;
			this.s = s;
			this.it = it;
		}
		
		protected RuleSuffixEvaluator(IndexedRule rule, int pos, OverwriteSubstitution s, Iterator<Iterable<Term[]>> it) {
			super(exec);
			this.rule = rule;
			this.head = rule.getHead();
			SimpleLiteral[] bd = new SimpleLiteral[rule.getBodySize()];
			for (int i = 0; i < bd.length; ++i) {
				bd[i] = rule.getBody(i);
			}
			this.body = bd;
			this.startPos = pos;
			this.s = s;
			this.it = it;
		}

		@Override
		public void doTask() throws EvaluationException {
			long start = 0;
			if (recordRuleDiagnostics) {
				start = System.currentTimeMillis();
			}
			Iterable<Term[]> tups = it.next();
			if (it.hasNext()) {
				exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, head, body, startPos, s.copy(), it));
			}
			try {
				for (Term[] tup : tups) {
					evaluate(tup);
				}
			} catch (UncheckedEvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating the rule: " + rule + "\n\n" + e.getMessage());
			}
			if (recordRuleDiagnostics) {
				long end = System.currentTimeMillis();
				Configuration.recordRuleTime(rule, end - start);
			}
		}

		void evaluate(Term[] ans) throws UncheckedEvaluationException {
			SimplePredicate p = (SimplePredicate) body[startPos];
			updateBinding(p, ans);
			int pos = startPos + 1;
			@SuppressWarnings("unchecked")
			Iterator<Term[]>[] stack = new Iterator[rule.getBodySize()];
			boolean movingRight = true;
			while (pos > startPos) {
				if (pos == body.length) {
					try {
						reportFact(head.normalize(s));
					} catch (EvaluationException e) {
						throw new UncheckedEvaluationException("Exception raised while evaluating the literal: "
								+ head + "\n\n" + e.getMessage());
					}
					pos--;
					movingRight = false;
				} else if (movingRight) {
					SimpleLiteral l = body[pos];
					try {
						switch (l.getTag()) {
						case ASSIGNMENT:
							((Assignment) l).assign(s);
							pos++;
							break;
						case CHECK:
							if (((Check) l).check(s)) {
								pos++;
							} else {
								pos--;
								movingRight = false;
							}
							break;
						case DESTRUCTOR:
							if (((Destructor) l).destruct(s)) {
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
									pos++;
								} else {
									pos--;
									movingRight = false;
								}
							} else {
								if (tups.hasNext()) {
									stack[pos] = tups.next().iterator();
									if (tups.hasNext()) {
										exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, head, body, pos, s.copy(), tups));
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
					Iterator<Term[]> it = stack[pos];
					if (it != null && it.hasNext()) {
						ans = it.next();
						updateBinding((SimplePredicate) rule.getBody(pos), ans);
						movingRight = true;
						pos++;
					} else {
						stack[pos] = null;
						pos--;
					}
				}
			}
		}

		void updateBinding(SimplePredicate p, Term[] ans) {
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
	class RulePrefixEvaluator extends AbstractFJPTask {

		final IndexedRule rule;

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
				Iterator<Iterable<Term[]>> tups = lookup(rule, pos, s).iterator();
				if (tups.hasNext()) {
					exec.recursivelyAddTask(new RuleSuffixEvaluator(rule, pos, s, tups));
				}
			} catch (EvaluationException e) {
				throw new EvaluationException(
						"Exception raised while evaluating the rule:\n" + rule + "\n\n" + e.getMessage());
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

	static class FactIterator implements Iterator<UserPredicate> {

		final RelationSymbol sym;
		final Iterator<Term[]> bindings;

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

	StopWatch recordRoundStart(Stratum stratum, int round) {
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

	void recordRoundEnd(Stratum stratum, int round, StopWatch watch) {
		if (watch == null) {
			return;
		}
		watch.stop();
		System.err.println("[END] Stratum " + stratum.getRank() + ", round " + round);
		System.err.println("Time: " + watch.getTime() + "ms");
	}

	StopWatch recordDbUpdateStart() {
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

	void recordDbUpdateEnd(StopWatch watch) {
		if (watch == null) {
			return;
		}
		watch.stop();
		Configuration.printRelSizes(System.err, "DELTA SIZE", deltaDb, false);
		System.err.println("[END] Updating DBs");
		System.err.println("Time: " + watch.getTime() + "ms");
	}

}
