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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.db.SortedIndexedFactDb.SortedIndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.magic.MagicSetTransformer;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.types.WellTypedProgram;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleRule;

public class NaiveEvaluation implements Evaluation {

	private final IndexedFactDb db;
	private final Map<RelationSymbol, Iterable<IndexedRule>> rules;
	private final UserPredicate query;
	
	public static NaiveEvaluation setup(WellTypedProgram prog) throws InvalidProgramException {
		MagicSetTransformer mst = new MagicSetTransformer(prog);
		BasicProgram magicProg;
		if (prog.hasQuery()) {
			magicProg = mst.transformForQuery(prog.getQuery(), true, true);
		} else {
			magicProg = mst.transform(true, true);
		}
		Set<RelationSymbol> allRelations = new HashSet<>(magicProg.getFactSymbols());
		allRelations.addAll(magicProg.getRuleSymbols());
		SortedIndexedFactDbBuilder dbb = new SortedIndexedFactDbBuilder(allRelations);
		Map<RelationSymbol, Iterable<IndexedRule>> rules = new HashMap<>();
		for (RelationSymbol sym : magicProg.getRuleSymbols()) {
			List<IndexedRule> rs = new ArrayList<>();
			for (BasicRule r : magicProg.getRules(sym)) {
				// XXX
			}
			rules.put(sym, rs);
		}
		IndexedFactDb db = dbb.build();
		for (RelationSymbol sym : magicProg.getFactSymbols()) {
			for (Term[] args : magicProg.getFacts(sym)) {
				db.add(sym, args);
			}
		}
		return new NaiveEvaluation(db, rules, magicProg.getQuery());
	}
	
	private NaiveEvaluation(IndexedFactDb db, Map<RelationSymbol, Iterable<IndexedRule>> rules, UserPredicate query) {
		this.db = db;
		this.rules = rules;
		this.query = query;
	}
	
	@Override
	public synchronized void run(int parallelism) throws EvaluationException {
		// TODO Auto-generated method stub

	}

	@Override
	public synchronized EvaluationResult getResult() {
		// TODO Auto-generated method stub
		return null;
	}

}
