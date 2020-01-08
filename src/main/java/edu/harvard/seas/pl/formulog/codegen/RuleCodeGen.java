package edu.harvard.seas.pl.formulog.codegen;

import java.util.ArrayList;

/*-
 * #%L
 * FormuLog
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

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.harvard.seas.pl.formulog.eval.IndexedRule;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.TodoException;
import edu.harvard.seas.pl.formulog.validating.ast.Assignment;
import edu.harvard.seas.pl.formulog.validating.ast.Check;
import edu.harvard.seas.pl.formulog.validating.ast.Destructor;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteral;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralTag;
import edu.harvard.seas.pl.formulog.validating.ast.SimpleLiteralVisitor;
import edu.harvard.seas.pl.formulog.validating.ast.SimplePredicate;

public class RuleCodeGen {

	private final CodeGenContext ctx;

	public RuleCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public Pair<List<CppStmt>, CppExpr> gen(IndexedRule rule) {
		return new Worker(rule).go();
	}

	private class Worker {

		private final IndexedRule rule;
		private int pos;

		public Worker(IndexedRule rule) {
			this.rule = rule;
		}

		private Pair<List<CppStmt>, CppExpr> go() {
			List<CppStmt> l = Collections.singletonList(mkOuterIf(mkIfBody()));
			return new Pair<>(l, CppConst.mkFalse());
		}

		private CppStmt mkOuterIf(List<CppStmt> body) {
			CppExpr guard = CppConst.mkTrue();
			int i = 0;
			for (SimpleLiteral l : rule) {
				if (l.getTag() == SimpleLiteralTag.PREDICATE) {
					SimplePredicate pred = (SimplePredicate) l;
					if (!pred.isNegated()) {
						CppIndex index = ctx.lookupIndex(pred.getSymbol(), rule.getDbIndex(i));
						CppExpr notEmpty = CppUnop.mkNot(index.mkIsEmpty());
						guard = CppBinop.mkLogAnd(guard, notEmpty);
					}
				}
				i++;
			}
			return CppIf.mk(guard, body);
		}
		
		private List<CppStmt> mkIfBody() {
			List<CppStmt> stmts = mkRulePrefix();
			if (pos > rule.getBodySize()) {
				throw new TodoException();
			}
			SimplePredicate pred = (SimplePredicate) rule.getBody(pos);
			assert !pred.isNegated();
			CppIndex index = ctx.lookupIndex(pred.getSymbol(), rule.getDbIndex(pos));
			stmts.add(CppDeclare.mk("part", index.mkPartition()));
			stmts.add(mkOuterLoop());
			return stmts;
		}
		
		private CppStmt mkOuterLoop() {
			CppExpr init = CppMethodCall.mk(CppVar.mk("part"), "begin");
			CppExpr guard = CppBinop.mkLt(CppVar.mk("it"), CppMethodCall.mk(CppVar.mk("part"), "end"));
			CppExpr update = CppUnop.mkPreIncr(CppVar.mk("it"));
			return CppFor.mk("it", init, guard, update, Collections.emptyList());
		}
		
		private List<CppStmt> mkRulePrefix() {
			List<CppStmt> acc = new ArrayList<>();
			SimpleLiteralVisitor<Void, Boolean> visitor = new SimpleLiteralVisitor<Void, Boolean>() {

				@Override
				public Boolean visit(Assignment assignment, Void input) {
					throw new TodoException();
				}

				@Override
				public Boolean visit(Check check, Void input) {
					throw new TodoException();
				}

				@Override
				public Boolean visit(Destructor destructor, Void input) {
					throw new TodoException();
				}

				@Override
				public Boolean visit(SimplePredicate predicate, Void input) {
					if (!predicate.isNegated()) {
						return false;
					}
					throw new TodoException();
				}
				
			};
			for (SimpleLiteral l : rule) {
				if (!l.accept(visitor, null)) {
					break;
				}
				pos++;
			}
			return acc;
		}

	}

}
