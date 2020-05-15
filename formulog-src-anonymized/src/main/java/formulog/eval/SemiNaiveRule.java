package formulog.eval;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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
import java.util.List;
import java.util.Set;

import formulog.ast.AbstractRule;
import formulog.ast.ComplexLiteral;
import formulog.ast.Rule;
import formulog.ast.Term;
import formulog.ast.UnificationPredicate;
import formulog.ast.UserPredicate;
import formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import formulog.symbols.AbstractWrappedRelationSymbol;
import formulog.symbols.RelationSymbol;
import formulog.util.Util;

public class SemiNaiveRule extends AbstractRule<UserPredicate, ComplexLiteral> {

	private SemiNaiveRule(UserPredicate head, List<ComplexLiteral> body) {
		super(head, body);
	}
	
	public static Set<SemiNaiveRule> make(Rule<UserPredicate, ComplexLiteral> rule, Set<RelationSymbol> stratumSymbols) {
		Set<SemiNaiveRule> rules = new HashSet<>();
		for (int i = 0; i < rule.getBodySize(); ++i) {
			boolean canBeDelta = rule.getBody(i).accept(new ComplexLiteralVisitor<Void, Boolean>() {

				@Override
				public Boolean visit(UnificationPredicate unificationPredicate, Void input) {
					return false;
				}

				@Override
				public Boolean visit(UserPredicate userPredicate, Void input) {
					return stratumSymbols.contains(userPredicate.getSymbol());
				}
				
			}, null);
			if (canBeDelta) {
				rules.add(make(rule, stratumSymbols, i));
			}
		}
		if (rules.isEmpty()) {
			rules.add(new SemiNaiveRule(rule.getHead(), Util.iterableToList(rule)));
		}
		return rules;
	}

	private static SemiNaiveRule make(Rule<UserPredicate, ComplexLiteral> rule, Set<RelationSymbol> stratumSymbols, int deltaIdx) {
		List<ComplexLiteral> body = new ArrayList<>();
		for (int i = 0; i < rule.getBodySize(); ++i) {
			ComplexLiteral l = rule.getBody(i);
			if (i == deltaIdx) {
				UserPredicate p = (UserPredicate) l;
				RelationSymbol sym = p.getSymbol();
				Term[] args = p.getArgs();
				l = UserPredicate.make(new DeltaSymbol(sym), args, p.isNegated());
			}
			body.add(l);
		}
		return new SemiNaiveRule(rule.getHead(), body);
	}
	
	public static class DeltaSymbol extends AbstractWrappedRelationSymbol<RelationSymbol> {

		public DeltaSymbol(RelationSymbol baseSymbol) {
			super(baseSymbol);
			assert baseSymbol.isIdbSymbol();
		}

		@Override
		public String toString() {
			return "delta:" + getBaseSymbol();
		}
		
	}
	
}
