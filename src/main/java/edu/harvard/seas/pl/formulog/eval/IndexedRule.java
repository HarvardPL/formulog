package edu.harvard.seas.pl.formulog.eval;

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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.Function;

import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.util.Util;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public class IndexedRule implements Rule<SimplePredicate, SimpleLiteral> {

	private final SimplePredicate head;
	private final List<SimpleLiteral> body;
	private final List<Integer> idxs;

	private IndexedRule(Rule<SimplePredicate, SimpleLiteral> rule, Function<SimplePredicate, Integer> makeIndex) {
		head = rule.getHead();
		body = Util.iterableToList(rule);
		idxs = createIndexes(makeIndex);
	}

	public static IndexedRule make(Rule<SimplePredicate, SimpleLiteral> rule,
			Function<SimplePredicate, Integer> makeIndex) {
		return new IndexedRule(rule, makeIndex);
	}

	private List<Integer> createIndexes(Function<SimplePredicate, Integer> makeIndex) {
		List<Integer> idxs = new ArrayList<>();
		for (SimpleLiteral a : body) {
			idxs.add(a.accept(new SimpleLiteralVisitor<Void, Integer>() {

				@Override
				public Integer visit(Assignment assignment, Void input) {
					return null;
				}

				@Override
				public Integer visit(Check check, Void input) {
					return null;
				}

				@Override
				public Integer visit(Destructor destructor, Void input) {
					return null;
				}

				@Override
				public Integer visit(SimplePredicate predicate, Void input) {
					return makeIndex.apply(predicate);
				}

			}, null));
		}
		return idxs;
	}

	@Override
	public SimplePredicate getHead() {
		return head;
	}

	@Override
	public int getBodySize() {
		return body.size();
	}

	@Override
	public SimpleLiteral getBody(int idx) {
		return body.get(idx);
	}

	public Integer getDbIndex(int idx) {
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
		int i = 0;
		for (Iterator<SimpleLiteral> it = body.iterator(); it.hasNext();) {
			Integer idx = idxs.get(i);
			if (idx != null) {
				sb.append(idx + ": ");
			}
			sb.append(it.next());
			if (it.hasNext()) {
				sb.append(",\n\t");
			}
			++i;
		}
		sb.append(".");
		return sb.toString();
	}

	@Override
	public Iterator<SimpleLiteral> iterator() {
		return body.iterator();
	}

}
