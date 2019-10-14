package edu.harvard.seas.pl.formulog.parsing;

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

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.BindingType;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class VariableCheckPass {

	private final SymbolManager sm;

	public VariableCheckPass(SymbolManager sm) {
		this.sm = sm;
	}

	public Term checkFunction(Iterable<Var> arguments, Term body) throws ParseException {
		PassContext ctx = new PassContext(arguments);
		Term newBody = ctx.checkTerm(body);
		ctx.checkCounts();
		return newBody;
	}
	
	public BasicRule checkRule(BasicRule r) throws ParseException {
		PassContext ctx = new PassContext();
		BasicRule newR = ctx.checkRule(r);
		try {
			ctx.checkCounts();
		} catch (ParseException e) {
			throw new ParseException("Variable usage error in rule: " + e.getMessage() + "\n\n" + r);
		}
		return newR;
	}

	public Term[] checkFact(Term[] fact) throws ParseException {
		PassContext ctx = new PassContext();
		Term[] newArgs = new Term[fact.length];
		for (int i = 0; i < fact.length; ++i) {
			newArgs[i] = ctx.checkTerm(fact[i]);
		}
		try {
			ctx.checkCounts();
		} catch (ParseException e) {
			throw new ParseException("Variable usage error in fact: " + e.getMessage());
		}
		return newArgs;
	}

	private class PassContext {

		private final Map<Var, Integer> cnts = new HashMap<>();
		private final Set<Var> fresh = new HashSet<>();

		public PassContext(Iterable<Var> seed) {
			for (Var x : seed) {
				int cnt = Util.lookupOrCreate(cnts, x, () -> 0);
				cnts.put(x, cnt + 1);
			}
		}
		
		public PassContext() {
			
		}
		
		public BasicRule checkRule(BasicRule r) {
			UserPredicate head = (UserPredicate) checkLiteral(r.getHead());
			List<ComplexLiteral> body = new ArrayList<>();
			for (ComplexLiteral l : r) {
				body.add(checkLiteral(l));
			}
			return BasicRule.make(head, body);
		}

		public ComplexLiteral checkLiteral(ComplexLiteral l) {
			Term[] newArgs = Terms.map(l.getArgs(), this::checkTerm);
			return l.accept(new ComplexLiteralVisitor<Void, ComplexLiteral>() {

				@Override
				public ComplexLiteral visit(UnificationPredicate pred, Void input) {
					return UnificationPredicate.make(newArgs[0], newArgs[1], pred.isNegated());
				}

				@Override
				public ComplexLiteral visit(UserPredicate pred, Void input) {
					return UserPredicate.make(pred.getSymbol(), newArgs, pred.isNegated());
				}

			}, null);
		}

		public Term checkTerm(Term t) {
			return t.accept(new TermVisitor<Void, Term>() {

				@Override
				public Term visit(Var x, Void in) {
					int cnt = Util.lookupOrCreate(cnts, x, () -> 0);
					cnts.put(x, cnt + 1);
					if (looksAnonymous(x)) {
						x = Var.fresh();
						fresh.add(x);
					}
					return x;
				}

				@Override
				public Term visit(Constructor c, Void in) {
					Term[] newArgs = Terms.map(c.getArgs(), PassContext.this::checkTerm);
					return c.copyWithNewArgs(newArgs);
				}

				@Override
				public Term visit(Primitive<?> p, Void in) {
					return p;
				}

				@Override
				public Term visit(Expr e, Void in) {
					return checkExpr(e);
				}

			}, null);
		}

		public Expr checkExpr(Expr e) {
			return e.accept(new ExprVisitor<Void, Expr>() {

				@Override
				public Expr visit(MatchExpr matchExpr, Void in) {
					Term scrutinee = checkTerm(matchExpr.getMatchee());
					List<MatchClause> clauses = new ArrayList<>();
					for (MatchClause cl : matchExpr) {
						Term lhs = checkTerm(cl.getLhs());
						Term rhs = checkTerm(cl.getRhs());
						clauses.add(MatchClause.make(lhs, rhs));
					}
					return MatchExpr.make(scrutinee, clauses);
				}

				@Override
				public Expr visit(FunctionCall funcCall, Void in) {
					Term[] newArgs = Terms.map(funcCall.getArgs(), PassContext.this::checkTerm);
					FunctionCallFactory factory = funcCall.getFactory();
					FunctionSymbol sym = funcCall.getSymbol();
					if (sym instanceof PredicateFunctionSymbol) {
						Pair<PredicateFunctionSymbol, Term[]> p = updatePlaceholder((PredicateFunctionSymbol) sym,
								newArgs);
						sym = p.fst();
						newArgs = p.snd();
						FunctionDefManager dm = factory.getDefManager();
						if (!dm.hasDefinition(sym)) {
							dm.register(new DummyFunctionDef(sym));
						}
					}
					return factory.make(sym, newArgs);
				}

			}, null);
		}

		private Pair<PredicateFunctionSymbol, Term[]> updatePlaceholder(PredicateFunctionSymbol placeholder,
				Term[] args) {
			BindingType[] bindings = new BindingType[args.length];
			List<Term> argsToKeep = new ArrayList<>();
			for (int i = 0; i < args.length; ++i) {
				Term arg = args[i];
				if (arg instanceof Var) {
					Var x = (Var) arg;
					if (fresh.contains(x)) {
						bindings[i] = BindingType.IGNORED;
					} else if (looksLikeHole(x)) {
						bindings[i] = BindingType.FREE;
						cnts.put(x, cnts.get(x) - 1);
					} else {
						bindings[i] = BindingType.BOUND;
						argsToKeep.add(arg);
					}
				} else {
					bindings[i] = BindingType.BOUND;
					argsToKeep.add(arg);
				}
			}
			PredicateFunctionSymbol sym = sm.createPredicateFunctionSymbol(placeholder.getPredicateSymbol(), bindings);
			args = argsToKeep.toArray(Terms.emptyArray());
			return new Pair<>(sym, args);
		}

		public void checkCounts() throws ParseException {
			for (Map.Entry<Var, Integer> e : cnts.entrySet()) {
				Var x = e.getKey();
				int cnt = e.getValue();
				if (looksLikeHole(x) && cnt > 0) {
					throw new ParseException("Can only use hole ?? as an argument to a predicate aggregate function.");
				} else if (looksLikeQuasiAnonymousVar(x) && cnt > 1) {
					throw new ParseException("Quasi-anonymous variable " + x + " occurs more than once.");
				} else if (!looksAnonymous(x) && cnt == 1) {
					throw new ParseException("Named variable " + x + " only occurs once.");
				}
			}
		}

	}

	private static boolean looksLikeHole(Var x) {
		return x.equals(Var.makeHole());
	}

	private static boolean looksAnonymous(Var x) {
		return x.toString().startsWith("_") || x.toString().startsWith("$");
	}

	private static boolean looksLikeTrueAnonymousVar(Var x) {
		return x.isUnderscore() || x.toString().startsWith("$");
	}

	private static boolean looksLikeQuasiAnonymousVar(Var x) {
		return looksAnonymous(x) && !looksLikeTrueAnonymousVar(x);
	}

}
