package edu.harvard.seas.pl.formulog.eval;

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

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb.SortedIndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.unification.OverwriteSubstitution;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.Stratifier;
import edu.harvard.seas.pl.formulog.validating.Stratum;
import edu.harvard.seas.pl.formulog.validating.ValidRule;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleConjunctExnVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleRule;

public class NaiveEvaluation implements Evaluation {

	private final IndexedFactDb db;
	private final Map<RelationSymbol, Iterable<IndexedRule>> rules;
	private final List<Stratum> strata;
	private final UserPredicate query;

	public static NaiveEvaluation setup(WellTypedProgram prog) throws InvalidProgramException {
		MagicSetTransformer mst = new MagicSetTransformer(prog);
		BasicProgram magicProg = mst.transform(true, true);
		
		List<Stratum> strata = new Stratifier(magicProg).stratify();
		for (Stratum stratum : strata) {
			if (stratum.hasRecursiveNegationOrAggregation()) {
				throw new InvalidProgramException("Cannot handle recursive negation or aggregation");
			}
		}
		
		Set<RelationSymbol> allRelations = new HashSet<>(magicProg.getFactSymbols());
		allRelations.addAll(magicProg.getRuleSymbols());
		SortedIndexedFactDbBuilder dbb = new SortedIndexedFactDbBuilder(allRelations);
		IndexedFactDbWrapper wrappedDb = new IndexedFactDbWrapper();
		PredicateFunctionSetter predFuncs = new PredicateFunctionSetter(
				magicProg.getFunctionCallFactory().getDefManager(), magicProg.getSymbolManager(), wrappedDb);
		Map<RelationSymbol, Iterable<IndexedRule>> rules = new HashMap<>();
		for (RelationSymbol sym : magicProg.getRuleSymbols()) {
			List<IndexedRule> rs = new ArrayList<>();
			for (BasicRule br : magicProg.getRules(sym)) {
				ValidRule vr = ValidRule.make(br, (p, vs) -> 0);
				predFuncs.preprocess(vr);
				SimpleRule sr = SimpleRule.make(vr);
				IndexedRule ir = IndexedRule.make(sr, dbb::makeIndex);
				rs.add(ir);
			}
			rules.put(sym, rs);
		}
		IndexedFactDb db = dbb.build();
		wrappedDb.set(db);

		for (RelationSymbol sym : magicProg.getFactSymbols()) {
			for (Term[] args : magicProg.getFacts(sym)) {
				try {
					db.add(sym, Terms.normalize(args, new SimpleSubstitution()));
				} catch (EvaluationException e) {
					UserPredicate p = UserPredicate.make(sym, args, false);
					throw new InvalidProgramException("Cannot normalize fact " + p + "\n" + e.getMessage());
				}
			}
		}
		return new NaiveEvaluation(db, rules, magicProg.getQuery(), strata);
	}

	private NaiveEvaluation(IndexedFactDb db, Map<RelationSymbol, Iterable<IndexedRule>> rules, UserPredicate query,
			List<Stratum> strata) {
		this.db = db;
		this.rules = rules;
		this.query = query;
		this.strata = strata;
	}

	@Override
	public synchronized void run(int parallelism) throws EvaluationException {
		for (Stratum stratum : strata) {
			evaluateStratum(stratum);
		}
	}

	private void evaluateStratum(Stratum stratum) throws EvaluationException {
		boolean changed = true;
		while (changed) {
			changed = false;
			for (RelationSymbol sym : stratum.getPredicateSyms()) {
				for (IndexedRule r : rules.get(sym)) {
					changed |= evaluateRule(r, 0, new OverwriteSubstitution());
				}

			}
		}
	}

	private boolean evaluateRule(IndexedRule r, int pos, OverwriteSubstitution s) throws EvaluationException {
		if (pos >= r.getBodySize()) {
			SimplePredicate hd = r.getHead().normalize(s);
			return db.add(hd.getSymbol(), Terms.normalize(hd.getArgs(), s));
		}
		return r.getBody(pos).accept(new SimpleConjunctExnVisitor<Void, Boolean, EvaluationException>() {

			@Override
			public Boolean visit(Assignment assignment, Void input) throws EvaluationException {
				assignment.assign(s);
				return evaluateRule(r, pos + 1, s);
			}

			@Override
			public Boolean visit(Check check, Void input) throws EvaluationException {
				return check.check(s) && evaluateRule(r, pos + 1, s);
			}

			@Override
			public Boolean visit(Destructor destructor, Void input) throws EvaluationException {
				return destructor.destruct(s) && evaluateRule(r, pos + 1, s);
			}

			@Override
			public Boolean visit(SimplePredicate predicate, Void input) throws EvaluationException {
				int idx = r.getDBIndex(pos);
				Term[] args = predicate.getArgs();
				Term[] key = new Term[args.length];
				boolean[] pat = predicate.getBindingPattern();
				for (int i = 0; i < args.length; ++i) {
					if (pat[i]) {
						key[i] = args[i].normalize(s);
					} else {
						key[i] = args[i];
					}
				}
				Set<Term[]> answers = db.get(key, idx);
				if (predicate.isNegated()) {
					return answers.isEmpty() && evaluateRule(r, pos + 1, s);
				} else {
					boolean changed = false;
					for (Term[] ans : answers) {
						for (int i = 0; i < pat.length; ++i) {
							if (!pat[i]) {
								s.put((Var) key[i], ans[i]);
							}
						}
						changed |= evaluateRule(r, pos + 1, s);
					}
					return changed;
				}
			}

		}, null);
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
		public Set<Term[]> getAll(RelationSymbol sym) {
			return db.getAll(sym);
		}

		@Override
		public Set<Term[]> get(Term[] key, int index) {
			return db.get(key, index);
		}

		@Override
		public boolean add(RelationSymbol sym, Term[] args) {
			return db.add(sym, args);
		}

		@Override
		public boolean hasFact(RelationSymbol sym, Term[] args) {
			return db.hasFact(sym, args);
		}

	}

}
