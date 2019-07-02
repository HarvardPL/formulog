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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.AtomVisitor;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.db.IndexedFactDB.IndexedFactDBBuilder;
import edu.harvard.seas.pl.formulog.util.Util;

public class IndexedRule implements Rule {

	private final Atom head;
	private final List<Atom> body;
	private final List<Integer> idxs;

	public IndexedRule(Rule rule, IndexedFactDBBuilder db) {
		head = rule.getHead();
		body = Util.iterableToList(rule.getBody());
		idxs = createIndexes(db);
	}

	private List<Integer> createIndexes(IndexedFactDBBuilder db) {
		List<Integer> idxs = new ArrayList<>();
		Set<Var> boundVars = new HashSet<>();
		for (Atom a : body) {
			idxs.add(a.visit(new AtomVisitor<Void, Integer>() {

				@Override
				public Integer visit(NormalAtom normalAtom, Void in) {
					return db.addIndex(normalAtom, boundVars);
				}

				@Override
				public Integer visit(UnifyAtom unifyAtom, Void in) {
					return null;
				}

			}, null));
			boundVars.addAll(Atoms.varSet(a));
		}
		return idxs;
	}

	@Override
	public Atom getHead() {
		return head;
	}

	@Override
	public Iterable<Atom> getBody() {
		return body;
	}

	@Override
	public int getBodySize() {
		return body.size();
	}

	@Override
	public Atom getBody(int idx) {
		return body.get(idx);
	}

	public Integer getDBIndex(int idx) {
		return idxs.get(idx);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(head);
		sb.append(" :-");
		if (body.size() == 1) {
			sb.append(" ");
		} else {
			sb.append("\n\t");
		}
		for (Iterator<Atom> it = body.iterator(); it.hasNext();) {
			sb.append(it.next());
			if (it.hasNext()) {
				sb.append(",\n\t");
			}
		}
		sb.append(".");
		return sb.toString();
	}

}
