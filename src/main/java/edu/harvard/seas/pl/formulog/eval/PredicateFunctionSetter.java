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

import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.db.IndexedFactDb;
import edu.harvard.seas.pl.formulog.db.IndexedFactDbBuilder;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;

public class PredicateFunctionSetter {

	private final FunctionDefManager defs;
	private final SymbolManager symbols;
	private final IndexedFactDbBuilder<?> dbb;
	private IndexedFactDb db;
	Set<FunctionSymbol> visitedFunctions = new HashSet<>();

	public PredicateFunctionSetter(FunctionDefManager funcs, SymbolManager symbols, IndexedFactDbBuilder<?> dbb) {
		this.defs = funcs;
		this.symbols = symbols;
		this.dbb = dbb;
	}
	
	public void setDb(IndexedFactDb db) {
		assert this.db == null;
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
		t.accept(tv, null);
	}

	private final TermVisitor<Void, Void> tv = new TermVisitor<Void, Void>() {

		@Override
		public Void visit(Var t, Void in) {
			return null;
		}

		@Override
		public Void visit(Constructor c, Void in) {
			for (Term arg : c.getArgs()) {
				arg.accept(this, in);
			}
			return null;
		}

		@Override
		public Void visit(Primitive<?> p, Void in) {
			return null;
		}

		@Override
		public Void visit(Expr e, Void in) {
			e.accept(ev, in);
			return null;
		}

	};

	private final ExprVisitor<Void, Void> ev = new ExprVisitor<Void, Void>() {

		@Override
		public Void visit(MatchExpr matchExpr, Void in) {
			matchExpr.getMatchee().accept(tv, in);
			for (MatchClause cl : matchExpr) {
				cl.getLhs().accept(tv, in);
				cl.getRhs().accept(tv, in);
			}
			return null;
		}

		@Override
		public Void visit(FunctionCall funcCall, Void in) {
			for (Term arg : funcCall.getArgs()) {
				arg.accept(tv, in);
			}
			FunctionSymbol sym = funcCall.getSymbol();
			if (!visitedFunctions.add(sym) || sym instanceof BuiltInFunctionSymbol) {
				return null;
			}
			FunctionDef def = defs.lookup(sym);
			if (sym instanceof PredicateFunctionSymbol) {
				DummyFunctionDef dummy = (DummyFunctionDef) def;
				setPredicateFunction(dummy);
			} else if (def instanceof UserFunctionDef) {
				((UserFunctionDef) def).getBody().accept(tv, in);
			}
			return null;
		}

		@Override
		public Void visit(LetFunExpr funcDef, Void in) {
			throw new AssertionError("impossible");
		}

		@Override
		public Void visit(Fold fold, Void in) {
			fold.getShamCall().accept(this, in);
			return null;
		}

	};

	private void setPredicateFunction(DummyFunctionDef def) {
		if (def.getDef() != null) {
			return;
		}
		PredicateFunctionSymbol sym = (PredicateFunctionSymbol) def.getSymbol();
		BindingType[] bindings = sym.getBindings();
		assert bindings != null;
		BindingType[] bindings2 = new BindingType[bindings.length];
		for (int i = 0; i < bindings.length; ++i) {
			bindings2[i] = bindings[i];
			if (bindings2[i].isIgnored()) {
				bindings2[i] = BindingType.FREE;
			}
		}
		int idx = dbb.makeIndex(sym.getPredicateSymbol(), bindings2);
		FunctorType type = sym.getCompileTimeType();
		Term[] paddedArgs = padArgs(sym);
		FunctionDef innerDef;
		if (type.getRetType().equals(BuiltInTypes.bool)) {
			innerDef = makePredicate(sym, paddedArgs, idx);
		} else {
			innerDef = makeAggregate(sym, paddedArgs, idx);
		}
		def.setDef(innerDef);
	}

	private FunctionDef makePredicate(PredicateFunctionSymbol funcSym, Term[] paddedArgs, int idx) {
		RelationSymbol predSym = funcSym.getPredicateSymbol();
		return new FunctionDef() {

			@Override
			public FunctionSymbol getSymbol() {
				return funcSym;
			}

			@Override
			public Term evaluate(Term[] args) throws EvaluationException {
				args = fillInPaddedArgs(funcSym, paddedArgs, args);
				if (db.get(predSym, args, idx).iterator().hasNext()) {
					return Constructors.trueTerm();
				} else {
					return Constructors.falseTerm();
				}
			}

		};
	}

	private FunctionDef makeAggregate(PredicateFunctionSymbol funcSym, Term[] paddedArgs, int idx) {
		RelationSymbol predSym = funcSym.getPredicateSymbol();
		int arity = 0;
		BindingType[] bindings = funcSym.getBindings();
		for (BindingType b : bindings) {
			if (b.isFree()) {
				arity++;
			}
		}
		final int arity2 = arity;
		ConstructorSymbol tupSym = (arity > 1) ? symbols.lookupTupleSymbol(arity) : null;
		return new FunctionDef() {

			@Override
			public FunctionSymbol getSymbol() {
				return funcSym;
			}

			@Override
			public Term evaluate(Term[] args) throws EvaluationException {
				args = fillInPaddedArgs(funcSym, paddedArgs, args);
				Term tail = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
				for (Term[] fact : db.get(predSym, args, idx)) {
					Term[] proj = new Term[arity2];
					int j = 0;
					for (int i = 0; i < bindings.length; ++i) {
						if (bindings[i].isFree()) {
							proj[j] = fact[i];
							++j;
						}
					}
					Term elt = tupSym == null ? proj[0] : Constructors.make(tupSym, proj);
					tail = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { elt, tail });
				}
				return tail;
			}

		};
	}
	
	private Term[] padArgs(PredicateFunctionSymbol funcSym) {
		RelationSymbol predSym = funcSym.getPredicateSymbol();
		Term[] padded = new Term[predSym.getArity()];
		for (int i = 0; i < padded.length; ++i) {
			padded[i] = Var.fresh();
		}
		return padded;
	}
	
	private Term[] fillInPaddedArgs(PredicateFunctionSymbol funcSym, Term[] paddedArgs, Term[] actualArgs) {
		RelationSymbol predSym = funcSym.getPredicateSymbol();
		Term[] newArgs = new Term[predSym.getArity()];
		int i = 0;
		int j = 0;
		for (BindingType b : funcSym.getBindings()) {
			if (b.isBound()) {
				newArgs[i] = actualArgs[j];
				j++;
			} else {
				newArgs[i] = paddedArgs[i];
			}
			i++;
		}
		return newArgs;
	}
	
}
