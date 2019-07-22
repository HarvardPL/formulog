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

import java.util.HashSet;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbolFactory.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;

public class PredicateFunctionSetter {

	private final FunctionDefManager defs;
	private final SymbolManager symbols;
	private final IndexedFactDb db;
	Set<FunctionSymbol> visitedFunctions = new HashSet<>();
	
	public PredicateFunctionSetter(FunctionDefManager funcs, SymbolManager symbols, IndexedFactDb db) {
		this.defs = funcs;
		this.symbols = symbols;
		this.db = db;
	}
	
	public void preprocess(Rule<UserPredicate, ComplexLiteral> r) {
		preprocess(r.getHead());
		for (ComplexLiteral l : r) {
			preprocess(l);
		}
	}
	
	public void preprocess(ComplexLiteral l) {
		for (Term arg : l.getArgs()) {
			preprocess(arg);
		}
	}
	
	public void preprocess(Term t) {
		t.visit(tv, null);
	}
	
	private final TermVisitor<Void, Void> tv = new TermVisitor<Void, Void>() {

		@Override
		public Void visit(Var t, Void in) {
			return null;
		}

		@Override
		public Void visit(Constructor c, Void in) {
			for (Term arg : c.getArgs()) {
				arg.visit(this, in);
			}
			return null;
		}

		@Override
		public Void visit(Primitive<?> p, Void in) {
			return null;
		}

		@Override
		public Void visit(Expr e, Void in) {
			e.visit(ev, in);
			return null;
		}
		
	};
	
	private final ExprVisitor<Void, Void> ev = new ExprVisitor<Void, Void>() {

		@Override
		public Void visit(MatchExpr matchExpr, Void in) {
			matchExpr.getMatchee().visit(tv, in);
			for (MatchClause cl : matchExpr) {
				cl.getLhs().visit(tv, in);
				cl.getRhs().visit(tv, in);
			}
			return null;
		}

		@Override
		public Void visit(FunctionCall funcCall, Void in) {
			for (Term arg : funcCall.getArgs()) {
				arg.visit(tv, in);
			}
			FunctionSymbol sym = funcCall.getSymbol();
			if (!visitedFunctions.add(sym)) {
				return null;
			}
			FunctionDef def = defs.lookup(sym);
			if (sym instanceof PredicateFunctionSymbol) {
				DummyFunctionDef dummy = (DummyFunctionDef) def;
				setPredicateFunction(dummy);
			} else if (def instanceof CustomFunctionDef) {
				((CustomFunctionDef) def).getBody().visit(tv, in);
			}
			return null;
		}
		
	};
	
	private void setPredicateFunction(DummyFunctionDef def) {
		if (def.getDef() != null) {
			return;
		}
		PredicateFunctionSymbol sym = (PredicateFunctionSymbol) def.getSymbol();
		if (sym.isReification()) {
			makeReifyPredicate(sym, def);
		} else {
			makeQueryPredicate(sym, def);
		}
	}

	private void makeQueryPredicate(PredicateFunctionSymbol sym, DummyFunctionDef def) {
		RelationSymbol predSym = sym.getPredicateSymbol();
		def.setDef(new FunctionDef() {

			@Override
			public FunctionSymbol getSymbol() {
				return def.getSymbol();
			}

			@Override
			public Term evaluate(Term[] args) throws EvaluationException {
				if (db.hasFact(predSym, args)) {
					return Constructors.trueTerm();
				} else {
					return Constructors.falseTerm();
				}
			}

		});
	}

	private void makeReifyPredicate(PredicateFunctionSymbol sym, DummyFunctionDef def) {
		RelationSymbol predSym = sym.getPredicateSymbol();
		int arity = predSym.getArity();
		ConstructorSymbol tupSym = (arity > 1) ? symbols.lookupTupleSymbol(arity) : null;
		def.setDef(new FunctionDef() {

			@Override
			public FunctionSymbol getSymbol() {
				return def.getSymbol();
			}

			@Override
			public Term evaluate(Term[] args) throws EvaluationException {
				Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
				for (Term[] fact : db.getAll(predSym)) {
					Term tuple = makeTuple(fact);
					t = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { tuple, t });
				}
				return t;
			}

			private Term makeTuple(Term[] args) {
				if (tupSym == null) {
					return args[0];
				} else {
					return Constructors.make(tupSym, args);
				}
			}

		});
	}
	
}
