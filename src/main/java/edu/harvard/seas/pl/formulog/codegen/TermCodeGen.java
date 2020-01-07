package edu.harvard.seas.pl.formulog.codegen;

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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.util.Pair;

public class TermCodeGen {

	private final CodeGenContext ctx;
	
	public TermCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public Pair<List<CppStmt>, CppExpr> gen(Term t, Map<Var, CppExpr> env) {
		return new Worker(new HashMap<>(env)).go(t);
	}
	
	public Pair<List<CppStmt>, List<CppExpr>> gen(List<Term> ts, Map<Var, CppExpr> env) {
		List<CppStmt> stmts = new ArrayList<>();
		List<CppExpr> exprs = new ArrayList<>();
		for (Term t : ts) {
			Pair<List<CppStmt>, CppExpr> p = gen(t, env);
			stmts.addAll(p.fst());
			exprs.add(p.snd());
		}
		return new Pair<>(stmts, exprs);
	}
	
	private class Worker {
		
		private final Map<Var, CppExpr> env;
		private final List<CppStmt> acc = new ArrayList<>();
		
		public Worker(Map<Var, CppExpr> env) {
			this.env = env;
		}
		
		public Pair<List<CppStmt>, CppExpr> go(Term t) {
			return new Pair<>(acc, t.accept(visitor, null));
		}
	
		private final TermVisitor<Void, CppExpr> visitor = new TermVisitor<Void, CppExpr>() {

			@Override
			public CppExpr visit(Var x, Void in) {
				throw new UnsupportedOperationException();
			}

			@Override
			public CppExpr visit(Constructor c, Void in) {
				throw new UnsupportedOperationException();
			}

			@Override
			public CppExpr visit(Primitive<?> p, Void in) {
				return BaseTerm.mk(p);
			}

			@Override
			public CppExpr visit(Expr e, Void in) {
				throw new UnsupportedOperationException();
			}
			
		};
		
	}

}
