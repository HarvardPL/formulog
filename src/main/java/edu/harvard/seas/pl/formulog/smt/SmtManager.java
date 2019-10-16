package edu.harvard.seas.pl.formulog.smt;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

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

import java.util.Map;
import java.util.Set;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicReferenceArray;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim.Status;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.util.Pair;

public class SmtManager {

	private final ArrayBlockingQueue<Z3Process> processes;
	private final Set<TypeSymbol> types = new HashSet<>();

	public SmtManager(Program<UserPredicate, BasicRule> prog) {
		int size = Configuration.smtParallelism;
		processes = new ArrayBlockingQueue<>(size);
		loadTypes(prog);
		for (int i = 0; i < size; ++i) {
			Z3Process proc = new Z3Process(prog.getSymbolManager());
			proc.start();
			processes.add(proc);
		}
	}

	public Pair<Status, Map<SolverVariable, Term>> check(SmtLibTerm assertion, int timeout) throws EvaluationException {
		Z3Process proc;
		try {
			proc = processes.take();
		} catch (InterruptedException e) {
			throw new EvaluationException(e);
		}
		Pair<Status, Map<SolverVariable, Term>> res = proc.check(assertion, timeout);
		processes.add(proc);
		return res;
	}

	private void loadTypes(Program<UserPredicate, BasicRule> prog) {
		TypeFinder tf = new TypeFinder();
		FunctionDefManager defs = prog.getFunctionCallFactory().getDefManager();
		for (FunctionSymbol sym : prog.getFunctionSymbols()) {
			if (defs.hasDefinition(sym)) {
				tf.exploreFunction(prog.getDef(sym));
			}
		}
		for (RelationSymbol sym : prog.getFactSymbols()) {
			tf.exploreFunctorType(sym.getCompileTimeType());
		}
		for (RelationSymbol sym : prog.getRuleSymbols()) {
			tf.exploreFunctorType(sym.getCompileTimeType());
			for (BasicRule r : prog.getRules(sym)) {
				tf.exploreRule(r);
			}
		}
	}

	private class TypeFinder {

		private final Set<FunctionSymbol> seenFuncs = new HashSet<>();
		private final Set<ConstructorSymbol> seenCtors = new HashSet<>();

		private final TermVisitor<Void, Void> tv = new TermVisitor<Void, Void>() {

			@Override
			public Void visit(Var t, Void in) {
				return null;
			}

			@Override
			public Void visit(Constructor c, Void in) {
				ConstructorSymbol sym = c.getSymbol();
				if (seenCtors.add(sym)) {
					exploreFunctorType(sym.getCompileTimeType());
				}
				for (Term arg : c.getArgs()) {
					exploreTerm(arg);
				}
				return null;
			}

			@Override
			public Void visit(Primitive<?> p, Void in) {
				return null;
			}

			@Override
			public Void visit(Expr e, Void in) {
				exploreExpr(e);
				return null;
			}

		};

		private final ExprVisitor<Void, Void> ev = new ExprVisitor<Void, Void>() {

			@Override
			public Void visit(MatchExpr matchExpr, Void in) {
				exploreTerm(matchExpr.getMatchee());
				for (MatchClause cl : matchExpr) {
					exploreTerm(cl.getLhs());
					exploreTerm(cl.getRhs());
				}
				return null;
			}

			@Override
			public Void visit(FunctionCall call, Void in) {
				FunctionSymbol sym = call.getSymbol();
				FunctionDefManager defs = call.getFactory().getDefManager();
				if (defs.hasDefinition(sym)) {
					exploreFunction(defs.lookup(sym));
				}
				for (Term arg : call.getArgs()) {
					exploreTerm(arg);
				}
				return null;
			}

		};

		public void exploreFunction(FunctionDef def) {
			FunctionSymbol sym = def.getSymbol();
			if (seenFuncs.add(sym)) {
				if (def instanceof UserFunctionDef) {
					exploreTerm(((UserFunctionDef) def).getBody());
				}
				exploreFunctorType(sym.getCompileTimeType());
			}

		}

		public void exploreRule(BasicRule r) {
			exploreLiteral(r.getHead());
			for (ComplexLiteral l : r) {
				exploreLiteral(l);
			}
		}

		private void exploreLiteral(ComplexLiteral l) {
			for (Term arg : l.getArgs()) {
				exploreTerm(arg);
			}
		}

		public void exploreTerm(Term term) {
			term.accept(tv, null);
		}

		private void exploreExpr(Expr expr) {
			expr.accept(ev, null);
		}

		public void exploreType(Type type) {
			type = TypeChecker.simplify(type);
			type.visit(new TypeVisitor<Void, Void>() {

				@Override
				public Void visit(TypeVar typeVar, Void in) {
					return null;
				}

				@Override
				public Void visit(AlgebraicDataType algebraicType, Void in) {
					TypeSymbol sym = algebraicType.getSymbol();
					if (types.add(sym)) {
						if (algebraicType.hasConstructors()) {
							for (ConstructorScheme cs : algebraicType.getConstructors()) {
								if (seenCtors.add(cs.getSymbol())) {
									for (Type type : cs.getTypeArgs()) {
										exploreType(type);
									}
								}
							}
						}
					}
					return null;
				}

				@Override
				public Void visit(OpaqueType opaqueType, Void in) {
					return null;
				}

				@Override
				public Void visit(TypeIndex typeIndex, Void in) {
					return null;
				}

			}, null);
		}

		public void exploreFunctorType(FunctorType ft) {
			for (Type type : ft.getArgTypes()) {
				exploreType(type);
			}
			exploreType(ft.getRetType());
		}
	}

}
