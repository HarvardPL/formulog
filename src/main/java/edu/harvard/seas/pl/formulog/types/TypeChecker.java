package edu.harvard.seas.pl.formulog.types;

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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralExnVisitor;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals.ComplexLiteralVisitor;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Fold;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.LetFunExpr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.NestedFunctionDef;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.InstantiatedPreConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.TodoException;
import edu.harvard.seas.pl.formulog.util.Triple;
import edu.harvard.seas.pl.formulog.util.Util;

public class TypeChecker {

	private final Program<UserPredicate, BasicRule> prog;
	private WellTypedProgram outputProgram;

	public TypeChecker(Program<UserPredicate, BasicRule> prog2) {
		this.prog = prog2;
	}

	public synchronized WellTypedProgram typeCheck() throws TypeException {
		if (outputProgram != null) {
			return outputProgram;
		}
		ExecutorService exec = Executors.newFixedThreadPool(Configuration.parallelism);
		Map<RelationSymbol, Set<Term[]>> newFacts = typeCheckFacts(exec);
		Map<FunctionSymbol, FunctionDef> newFuncs = typeCheckFunctions(exec);
		FunctionDefManager dm = prog.getFunctionCallFactory().getDefManager();
		for (FunctionDef func : newFuncs.values()) {
			dm.reregister(func);
		}
		Map<RelationSymbol, Set<BasicRule>> newRules = typeCheckRules(exec);
		UserPredicate newQuery = typeCheckQuery();
		exec.shutdown();
		outputProgram = new WellTypedProgram() {

			@Override
			public Set<FunctionSymbol> getFunctionSymbols() {
				return newFuncs.keySet();
			}

			@Override
			public Set<RelationSymbol> getFactSymbols() {
				return Collections.unmodifiableSet(newFacts.keySet());
			}

			@Override
			public Set<RelationSymbol> getRuleSymbols() {
				return Collections.unmodifiableSet(newRules.keySet());
			}

			@Override
			public FunctionDef getDef(FunctionSymbol sym) {
				return newFuncs.get(sym);
			}

			@Override
			public Set<Term[]> getFacts(RelationSymbol sym) {
				if (!sym.isEdbSymbol()) {
					throw new IllegalArgumentException();
				}
				if (!newFacts.containsKey(sym)) {
					throw new IllegalArgumentException();
				}
				return newFacts.get(sym);
			}

			@Override
			public Set<BasicRule> getRules(RelationSymbol sym) {
				if (!sym.isIdbSymbol()) {
					throw new IllegalArgumentException();
				}
				if (!newRules.containsKey(sym)) {
					throw new IllegalArgumentException();
				}
				return newRules.get(sym);
			}

			@Override
			public SymbolManager getSymbolManager() {
				return prog.getSymbolManager();
			}

			@Override
			public boolean hasQuery() {
				return newQuery != null;
			}

			@Override
			public UserPredicate getQuery() {
				return newQuery;
			}

			@Override
			public FunctionCallFactory getFunctionCallFactory() {
				return prog.getFunctionCallFactory();
			}

			@Override
			public Set<ConstructorSymbol> getUninterpretedFunctionSymbols() {
				return prog.getUninterpretedFunctionSymbols();
			}

			@Override
			public Set<TypeSymbol> getTypeSymbols() {
				return prog.getTypeSymbols();
			}

		};
		return outputProgram;
	}

	private UserPredicate typeCheckQuery() throws TypeException {
		if (prog.hasQuery()) {
			TypeCheckerContext ctx = new TypeCheckerContext();
			return ctx.typeCheckQuery(prog.getQuery());
		}
		return null;
	}

	private static <K, V> Map<K, V> mapFromFutures(Map<K, Future<V>> futures) throws TypeException {
		try {
			return Util.fillMapWithFutures(futures, new HashMap<>());
		} catch (InterruptedException | ExecutionException e) {
			throw new TypeException(e);
		}
	}

	private Map<RelationSymbol, Set<Term[]>> typeCheckFacts(ExecutorService exec) throws TypeException {
		Map<RelationSymbol, Future<Set<Term[]>>> futures = new HashMap<>();
		for (RelationSymbol sym : prog.getFactSymbols()) {
			Future<Set<Term[]>> fut = exec.submit(new Callable<Set<Term[]>>() {

				@Override
				public Set<Term[]> call() throws Exception {
					// Can use same type checker context for all, since there should be neither
					// program variables (in a fact) or type variables (in a relation type).
					// Addendum: there can be program variables (in type index positions),
					// but they should be unique.
					TypeCheckerContext ctx = new TypeCheckerContext();
					Set<Term[]> s = new HashSet<>();
					for (Term[] args : prog.getFacts(sym)) {
						s.add(ctx.typeCheckFact(sym, args));
					}
					return s;
				}

			});
			futures.put(sym, fut);
		}
		return mapFromFutures(futures);
	}

	private Map<RelationSymbol, Set<BasicRule>> typeCheckRules(ExecutorService exec) throws TypeException {
		Map<RelationSymbol, Future<Set<BasicRule>>> futures = new HashMap<>();
		for (RelationSymbol sym : prog.getRuleSymbols()) {
			Future<Set<BasicRule>> fut = exec.submit(new Callable<Set<BasicRule>>() {

				@Override
				public Set<BasicRule> call() throws Exception {
					Set<BasicRule> s = new HashSet<>();
					for (BasicRule r : prog.getRules(sym)) {
						TypeCheckerContext ctx = new TypeCheckerContext();
						s.add(ctx.typeCheckRule(r));
					}
					return s;
				}

			});
			futures.put(sym, fut);
		}
		return mapFromFutures(futures);
	}

	private Map<FunctionSymbol, FunctionDef> typeCheckFunctions(ExecutorService exec) throws TypeException {
		Map<FunctionSymbol, Future<FunctionDef>> futures = new HashMap<>();
		List<FunctionDef> nonUserFunctions = new ArrayList<>();
		for (FunctionSymbol sym : prog.getFunctionSymbols()) {
			FunctionDef def = prog.getDef(sym);
			if (def instanceof UserFunctionDef) {
				Future<FunctionDef> fut = exec.submit(new Callable<FunctionDef>() {

					@Override
					public FunctionDef call() throws Exception {
						TypeCheckerContext ctx = new TypeCheckerContext();
						return ctx.typeCheckFunction((UserFunctionDef) def);
					}

				});
				futures.put(sym, fut);
			} else {
				nonUserFunctions.add(def);
			}
		}
		Map<FunctionSymbol, FunctionDef> m = mapFromFutures(futures);
		for (FunctionDef def : nonUserFunctions) {
			m.put(def.getSymbol(), def);
		}
		return m;
	}

	private class TypeCheckerContext {

		private final Deque<Triple<Term, Type, Type>> constraints = new ArrayDeque<>();
		private final Deque<Triple<Term, Type, Type>> formulaConstraints = new ArrayDeque<>();
		private final Map<TypeVar, Type> typeVars = new HashMap<>();
		private final Deque<Pair<Constructor, Type>> smtEqsToResolve = new ArrayDeque<>();
		private String error;

		public Term[] typeCheckFact(RelationSymbol sym, Term[] args) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(sym, args, subst);
			if (!checkConstraints()) {
				throw new TypeException("Type error in fact: " + UserPredicate.make(sym, args, false) + "\n" + error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return Terms.mapExn(args, t -> t.accept(termRewriter, m));
		}

		private ComplexLiteral rewriteLiteral(ComplexLiteral l, Substitution m) throws TypeException {
			Term[] args = Terms.mapExn(l.getArgs(), t -> t.accept(termRewriter, m));
			return l.accept(new ComplexLiteralExnVisitor<Void, ComplexLiteral, TypeException>() {

				@Override
				public ComplexLiteral visit(UnificationPredicate pred, Void input) throws TypeException {
					return UnificationPredicate.make(args[0], args[1], pred.isNegated());
				}

				@Override
				public ComplexLiteral visit(UserPredicate pred, Void input) throws TypeException {
					return UserPredicate.make(pred.getSymbol(), args, pred.isNegated());
				}

			}, null);
		}

		public UserPredicate typeCheckQuery(UserPredicate q) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(q, subst);
			if (!checkConstraints()) {
				throw new TypeException("Type error in query: " + q + "\n" + error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return (UserPredicate) rewriteLiteral(q, m);
		}

		public BasicRule typeCheckRule(Rule<UserPredicate, ComplexLiteral> r) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			processAtoms(r, subst);
			genConstraints(r.getHead(), subst);
			if (!checkConstraints()) {
				String msg = "Type error in rule:\n";
				msg += r + "\n";
				msg += error;
				throw new TypeException(msg);
			}
			Substitution m = makeIndexSubstitution(subst);
			UserPredicate newHead = (UserPredicate) rewriteLiteral(r.getHead(), m);
			List<ComplexLiteral> newBody = new ArrayList<>();
			for (ComplexLiteral a : r) {
				newBody.add(rewriteLiteral(a, m));
			}
			return BasicRule.make(newHead, newBody);
		}

		private Substitution makeIndexSubstitution(Map<Var, Type> subst) {
			Substitution m = new SimpleSubstitution();
			for (Map.Entry<Var, Type> e : subst.entrySet()) {
				Var x = e.getKey();
				Type t = lookupType(e.getValue());
				if (t instanceof TypeIndex) {
					int idx = ((TypeIndex) t).getIndex();
					ConstructorSymbol csym = prog.getSymbolManager().lookupIndexConstructorSymbol(idx);
					Term c = Constructors.make(csym, Terms.singletonArray(I32.make(idx)));
					m.put(x, c);
				}
			}
			return m;
		}

		public UserFunctionDef typeCheckFunction(UserFunctionDef functionDef) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(functionDef, subst);
			if (!checkConstraints()) {
				throw new TypeException("Type error in function: " + functionDef.getSymbol() + "\n"
						+ functionDef.getBody() + "\n" + error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return UserFunctionDef.get(functionDef.getSymbol(), functionDef.getParams(),
					functionDef.getBody().accept(termRewriter, m));
		}

		private void processAtoms(Iterable<ComplexLiteral> atoms, Map<Var, Type> subst) {
			for (ComplexLiteral a : atoms) {
				genConstraints(a, subst);
			}
		}

		private void genConstraints(RelationSymbol sym, Term[] args, Map<Var, Type> subst) {
			FunctorType ftype = sym.getCompileTimeType().freshen();
			assert ftype.getArgTypes().size() == args.length;
			int i = 0;
			for (Type type : ftype.getArgTypes()) {
				genConstraints(args[i], type, subst, false);
				++i;
			}
		}

		private void genConstraints(ComplexLiteral a, Map<Var, Type> subst) {
			a.accept(new ComplexLiteralVisitor<Void, Void>() {

				@Override
				public Void visit(UserPredicate normalAtom, Void in) {
					genConstraints(normalAtom.getSymbol(), normalAtom.getArgs(), subst);
					return null;
				}

				@Override
				public Void visit(UnificationPredicate unifyAtom, Void in) {
					TypeVar var = TypeVar.fresh();
					genConstraints(unifyAtom.getLhs(), var, subst, false);
					genConstraints(unifyAtom.getRhs(), var, subst, false);
					return null;
				}

			}, null);
		}

		private void genConstraints(UserFunctionDef def, Map<Var, Type> subst) {
			FunctionSymbol sym = def.getSymbol();
			genConstraints(sym, def.getParams(), def.getBody(), subst);
		}

		private void genConstraints(FunctionSymbol sym, List<Var> params, Term body, Map<Var, Type> subst) {
			FunctorType scheme = sym.getCompileTimeType().freshen();
			Map<TypeVar, OpaqueType> opaqueTypes = new HashMap<>();
			List<Type> argTypes = scheme.getArgTypes();
			for (Type t : argTypes) {
				if (t instanceof TypeVar) {
					addConstraint(null, t, Util.lookupOrCreate(opaqueTypes, (TypeVar) t, () -> OpaqueType.get()),
							false);
				}
			}
			Type r = scheme.getRetType();
			if (r instanceof TypeVar) {
				addConstraint(null, r, Util.lookupOrCreate(opaqueTypes, (TypeVar) r, () -> OpaqueType.get()), false);
			}
			for (int i = 0; i < params.size(); ++i) {
				subst.put(params.get(i), argTypes.get(i));
			}
			genConstraints(body, r, subst, false);
		}

		private void genConstraintsForExpr(Expr e, Type exprType, Map<Var, Type> varTypes, boolean inFormula) {
			e.accept(new ExprVisitor<Void, Void>() {

				@Override
				public Void visit(MatchExpr matchExpr, Void in) {
					assert !inFormula;
					TypeVar guardType = TypeVar.fresh();
					Term guard = matchExpr.getMatchee();
					genConstraints(guard, guardType, varTypes, inFormula);
					for (MatchClause cl : matchExpr) {
						genConstraints(cl.getLhs(), guardType, varTypes, inFormula);
						genConstraints(cl.getRhs(), exprType, varTypes, inFormula);
					}
					return null;
				}

				@Override
				public Void visit(FunctionCall funcCall, Void in) {
					genConstraintsForFunctionCall(funcCall, exprType, varTypes, inFormula);
					return null;
				}

				@Override
				public Void visit(LetFunExpr letFun, Void in) {
					assert !inFormula;
					for (NestedFunctionDef def : letFun.getDefs()) {
						def = def.freshen();
						genConstraints(def.getSymbol(), def.getParams(), def.getBody(), varTypes);
					}
					genConstraints(letFun.getLetBody(), exprType, varTypes, inFormula);
					return null;
				}

				@Override
				public Void visit(Fold fold, Void in) {
					assert !inFormula;
					FunctionSymbol sym = fold.getFunction();
					Term[] args = fold.getArgs();
					assert sym.getArity() == args.length && args.length == 2;
					Type itemType = TypeVar.fresh();
					Type listType = BuiltInTypes.list(itemType);
					FunctorType funType = sym.getCompileTimeType().freshen();
					genConstraints(args[0], exprType, varTypes, inFormula);
					genConstraints(args[0], funType.getArgTypes().get(0), varTypes, inFormula);
					genConstraints(args[1], listType, varTypes, inFormula);
					addConstraint(args[1], itemType, funType.getArgTypes().get(1), inFormula);
					addConstraint(fold, exprType, funType.getRetType(), inFormula);
					return null;
				}

			}, null);
		}

		private void addConstraint(Term t, Type t1, Type t2, boolean inFormula) {
			Triple<Term, Type, Type> constraint = new Triple<>(t, t1, t2);
			if (inFormula) {
				formulaConstraints.add(constraint);
			} else {
				constraints.add(constraint);
			}
		}

		private void genConstraints(Term t, Type ttype, Map<Var, Type> subst, boolean inFormula) {
			t.accept(new TermVisitor<Void, Void>() {

				@Override
				public Void visit(Var t, Void in) {
					genConstraintsForVar(t, ttype, subst, inFormula);
					return null;
				}

				@Override
				public Void visit(Constructor t, Void in) {
					genConstraintsForConstructor(t, ttype, subst, inFormula);
					return null;
				}

				@Override
				public Void visit(Primitive<?> prim, Void in) {
					genConstraintsForPrimitive(prim, ttype, inFormula);
					return null;
				}

				@Override
				public Void visit(Expr expr, Void in) {
					genConstraintsForExpr(expr, ttype, subst, inFormula);
					return null;
				}

			}, null);
		}

		private void genConstraintsForVar(Var t, Type ttype, Map<Var, Type> subst, boolean inFormula) {
			Type s = Util.lookupOrCreate(subst, t, () -> TypeVar.fresh());
			addConstraint(t, s, ttype, inFormula);
		}

		private void genConstraintsForPrimitive(Primitive<?> t, Type ttype, boolean inFormula) {
			addConstraint(t, ttype, t.getType(), inFormula);
		}

		private void genConstraintsForConstructor(Constructor t, Type ttype, Map<Var, Type> subst, boolean inFormula) {
			boolean wasInFormula = inFormula;
			ConstructorSymbol cnstrSym = t.getSymbol();
			if (cnstrSym.equals(BuiltInConstructorSymbol.ENTER_FORMULA)) {
				assert !wasInFormula;
				inFormula = true;
			}
			if (cnstrSym.equals(BuiltInConstructorSymbol.EXIT_FORMULA)) {
				inFormula = false;
			}
			FunctorType cnstrType = cnstrSym.getCompileTimeType().freshen();
			Term[] args = t.getArgs();
			List<Type> argTypes = cnstrType.getArgTypes();
			if (cnstrSym instanceof InstantiatedPreConstructorSymbol) {
				throw new TodoException();
//				if (cnstrSym.equals(BuiltInConstructorSymbol.FORMULA_EQ)) {
//					smtEqsToResolve.add(new Pair<>(t, argTypes.get(0)));
//				}
			}
			for (int i = 0; i < args.length; ++i) {
				Type argType = argTypes.get(i);
				genConstraints(args[i], argType, subst, inFormula);
			}
			addConstraint(t, cnstrType.getRetType(), ttype, wasInFormula);
		}

		private void genConstraintsForFunctionCall(FunctionCall function, Type ttype, Map<Var, Type> subst,
				boolean inFormula) {
			FunctorType funType = (FunctorType) function.getSymbol().getCompileTimeType().freshen();
			Term[] args = function.getArgs();
			List<Type> argTypes = funType.getArgTypes();
			for (int i = 0; i < args.length; ++i) {
				genConstraints(args[i], argTypes.get(i), subst, inFormula);
			}
			addConstraint(function, funType.getRetType(), ttype, inFormula);
		}

		private boolean checkConstraints() {
			Set<Type> typesInFormulae = new HashSet<>();
			for (Triple<Term, Type, Type> p : formulaConstraints) {
				typesInFormulae.add(p.second);
			}
			// First try to unify constraints generated outside of formula and then
			// constraints generated inside formula. This might generate more constraints,
			// but all of them will be treated as being in a non-formula context.
			boolean ok = checkConstraints(false) && checkConstraints(true) && checkConstraints(false);
			assert !ok || constraints.isEmpty() && formulaConstraints.isEmpty();
			ok = ok && checkTypesInFormulae(typesInFormulae);
			return ok;
		}

		private boolean checkTypesInFormulae(Set<Type> types) {
			for (Type ty : types) {
				if (!checkTypeInFormula(ty)) {
					return false;
				}
			}
			return true;
		}

		private boolean checkTypeInFormula(Type ty) {
			return lookupType(ty).accept(new TypeVisitor<Void, Boolean>() {

				@Override
				public Boolean visit(TypeVar typeVar, Void in) {
					return true;
				}

				@Override
				public Boolean visit(AlgebraicDataType algebraicType, Void in) {
					if (algebraicType.getSymbol().equals(BuiltInTypeSymbol.MODEL_TYPE)) {
						error = "Models are not allowed in formulae.";
						return false;
					}
					for (Type arg : algebraicType.getTypeArgs()) {
						if (!arg.accept(this, in)) {
							return false;
						}
					}
					return true;
				}

				@Override
				public Boolean visit(OpaqueType opaqueType, Void in) {
					return true;
				}

				@Override
				public Boolean visit(TypeIndex typeIndex, Void in) {
					return true;
				}

			}, null);
		}

		private boolean checkConstraints(boolean inFormulaContext) {
			Deque<Triple<Term, Type, Type>> q = inFormulaContext ? formulaConstraints : constraints;
			while (!q.isEmpty()) {
				Triple<Term, Type, Type> constraint = q.pop();
				Type type1 = lookupType(constraint.second);
				Type type2 = lookupType(constraint.third);
				if (inFormulaContext) {
					type1 = simplify(type1);
					type2 = simplify(type2);
				}
				if (type1.isVar() || type2.isVar()) {
					if (!handleVars(type1, type2)) {
						return false;
					}
				} else if (!unify(constraint.first, type1, type2)) {
					error = "Cannot unify " + type1 + " and " + type2;
					error += "\nProblematic term: " + constraint.first;
					return false;
				}
			}
			return true;
		}

		private boolean handleVars(Type type1, Type type2) {
			if (type1.isVar() && type2.isVar()) {
				addBinding((TypeVar) type1, type2, typeVars);
				return true;
			}

			TypeVar var;
			Type other;
			if (type1.isVar()) {
				var = (TypeVar) type1;
				other = type2;
			} else {
				assert type2.isVar();
				var = (TypeVar) type2;
				other = type1;
			}
			// Occurs check
			if (Types.getTypeVars(other).contains(var)) {
				return false;
			}
			typeVars.put(var, other);
			return true;
		}

		private boolean unify(Term t, Type type1, Type type2) {
			return type1.accept(new TypeVisitor<Type, Boolean>() {

				@Override
				public Boolean visit(TypeVar typeVar, Type other) {
					throw new AssertionError("unreachable");
				}

				@Override
				public Boolean visit(AlgebraicDataType typeRef, Type other) {
					if (!(other instanceof AlgebraicDataType)) {
						return false;
					}
					AlgebraicDataType otherTypeRef = (AlgebraicDataType) other;
					if (!typeRef.getSymbol().equals(otherTypeRef.getSymbol())) {
						return false;
					}
					List<Type> args1 = typeRef.getTypeArgs();
					List<Type> args2 = otherTypeRef.getTypeArgs();
					for (int i = 0; i < args1.size(); ++i) {
						addConstraint(t, args1.get(i), args2.get(i), false);
					}
					return true;
				}

				@Override
				public Boolean visit(OpaqueType opaqueType, Type other) {
					return opaqueType.equals(other);
				}

				@Override
				public Boolean visit(TypeIndex typeIndex, Type other) {
					return typeIndex.equals(other);
				}

			}, type2);
		}

		private Type lookupType(Type t) {
			return TypeChecker.lookupType(t, typeVars);
		}

		private final TermVisitorExn<Substitution, Term, TypeException> termRewriter = new TermVisitorExn<Substitution, Term, TypeException>() {

			@Override
			public Term visit(Var x, Substitution subst) throws TypeException {
				if (subst.containsKey(x)) {
					return subst.get(x);
				}
				return x;
			}

			@Override
			public Term visit(Constructor c, Substitution subst) throws TypeException {
				ConstructorSymbol sym = c.getSymbol();
				if (sym instanceof InstantiatedPreConstructorSymbol) {
					throw new TodoException();
//					if (sym.equals(BuiltInConstructorSymbol.FORMULA_EQ)) {
//						Pair<Constructor, Type> p = smtEqsToResolve.removeFirst();
//						Type eltType = simplify(lookupType(p.snd()));
//						if (Types.containsTypeVarOrOpaqueType(eltType)) {
//							throw new TypeException("Cannot determine element type in solver equality: " + p.fst());
//						}
//						sym = prog.getSymbolManager().lookupSmtEqSymbol(eltType);
//					}
				}
				Term[] args = c.getArgs();
				Term[] newArgs = new Term[args.length];
				for (int i = 0; i < args.length; ++i) {
					newArgs[i] = args[i].accept(this, subst);
				}
				if (sym.equals(BuiltInConstructorSymbol.ENTER_FORMULA)
						|| sym.equals(BuiltInConstructorSymbol.EXIT_FORMULA)) {
					return newArgs[0];
				}
				return Constructors.make(sym, newArgs);
			}

			@Override
			public Term visit(Primitive<?> p, Substitution subst) throws TypeException {
				return p;
			}

			@Override
			public Term visit(Expr e, Substitution subst) throws TypeException {
				return e.accept(exprRewriter, subst);
			}

		};

		private final Map<FunctionSymbol, FunctionSymbol> topLevelSymbolOfNestedFunction = new HashMap<>();
		private final Map<FunctionSymbol, List<Var>> capturedVarsOfNestedFunction = new HashMap<>();

		private final ExprVisitorExn<Substitution, Term, TypeException> exprRewriter = new ExprVisitorExn<Substitution, Term, TypeException>() {

			@Override
			public Term visit(MatchExpr matchExpr, Substitution subst) throws TypeException {
				Term scrutinee = matchExpr.getMatchee().accept(termRewriter, subst);
				List<MatchClause> clauses = new ArrayList<>();
				for (MatchClause cl : matchExpr) {
					Term lhs = cl.getLhs().accept(termRewriter, subst);
					Term rhs = cl.getRhs().accept(termRewriter, subst);
					clauses.add(MatchClause.make(lhs, rhs));
				}
				return MatchExpr.make(scrutinee, clauses);
			}

			@Override
			public Term visit(FunctionCall funcCall, Substitution subst) throws TypeException {
				FunctionSymbol sym = funcCall.getSymbol();
				List<Var> capturedVars = Collections.emptyList();
				if (topLevelSymbolOfNestedFunction.containsKey(sym)) {
					sym = topLevelSymbolOfNestedFunction.get(sym);
					capturedVars = capturedVarsOfNestedFunction.get(sym);
				}
				Term[] args = funcCall.getArgs();
				Term[] newArgs = new Term[args.length + capturedVars.size()];
				int i = 0;
				for (; i < args.length; ++i) {
					newArgs[i] = args[i].accept(termRewriter, subst);
				}
				for (Var x : capturedVars) {
					newArgs[i] = x;
					++i;
				}
				return prog.getFunctionCallFactory().make(sym, newArgs);
			}

			@Override
			public Term visit(LetFunExpr letFun, Substitution in) throws TypeException {
				Set<NestedFunctionDef> defs = new HashSet<>();
				Set<Var> capturedVarSet = new HashSet<>();
				for (NestedFunctionDef def : letFun.getDefs()) {
					def = firstRewritingPass(def, in);
					defs.add(def);
					Set<Var> s = def.getBody().varSet();
					s.removeAll(def.getParams());
					capturedVarSet.addAll(s);
				}
				List<Var> capturedVars = new ArrayList<>(capturedVarSet);
				for (NestedFunctionDef def : defs) {
					FunctionSymbol oldSym = def.getSymbol();
					int newArity = oldSym.getArity() + capturedVarSet.size();
					FunctionSymbol newSym = prog.getSymbolManager().createFunctionSymbol(oldSym + "$toplevel", newArity,
							null);
					topLevelSymbolOfNestedFunction.put(oldSym, newSym);
					capturedVarsOfNestedFunction.put(newSym, capturedVars);
				}
				for (NestedFunctionDef def : defs) {
					FunctionSymbol sym = topLevelSymbolOfNestedFunction.get(def.getSymbol());
					List<Var> params = new ArrayList<>(def.getParams());
					params.addAll(capturedVars);
					FunctionDef newDef = UserFunctionDef.get(sym, params, def.getBody().accept(termRewriter, in));
					prog.getFunctionCallFactory().getDefManager().register(newDef);
				}
				return letFun.getLetBody().accept(termRewriter, in);
			}

			NestedFunctionDef firstRewritingPass(NestedFunctionDef def, Substitution subst) throws TypeException {
				Substitution s = new SimpleSubstitution();
				List<Var> newParams = new ArrayList<>();
				for (Var param : def.getParams()) {
					if (!s.containsKey(param)) {
						Var newParam = Var.fresh(param.toString());
						s.put(param, newParam);
						newParams.add(newParam);
					} else {
						newParams.add((Var) s.get(param));
					}

				}
				Term body = def.getBody().applySubstitution(s).accept(termRewriter, subst);
				return NestedFunctionDef.make(def.getSymbol(), newParams, body);
			}

			@Override
			public Term visit(Fold fold, Substitution in) throws TypeException {
				FunctionCall f = (FunctionCall) fold.getShamCall().accept(this, in);
				return Fold.mk(f.getSymbol(), f.getArgs(), f.getFactory());
			}

		};

	}

	// XXX This and lookupType should be factored into a class for type
	// substitutions.
	public static void addBinding(TypeVar x, Type t, Map<TypeVar, Type> subst) {
		if (t instanceof TypeVar) {
			// Avoid cycles in map
			TypeVar y = (TypeVar) t;
			if (x.compareTo(y) > 0) {
				subst.put(x, y);
			} else if (x.compareTo(y) < 0) {
				subst.put(y, x);
			}
		} else {
			subst.put(x, t);
		}
	}

	public static Type lookupType(Type t, Map<TypeVar, Type> subst) {
		return t.accept(new TypeVisitor<Void, Type>() {

			@Override
			public Type visit(TypeVar typeVar, Void in) {
				if (subst.containsKey(typeVar)) {
					return subst.get(typeVar).accept(this, in);
				}
				return typeVar;
			}

			@Override
			public Type visit(AlgebraicDataType algebraicType, Void in) {
				List<Type> args = Util.map(algebraicType.getTypeArgs(), t -> t.accept(this, in));
				return AlgebraicDataType.make(algebraicType.getSymbol(), args);
			}

			@Override
			public Type visit(OpaqueType opaqueType, Void in) {
				return opaqueType;
			}

			@Override
			public Type visit(TypeIndex typeIndex, Void in) {
				return typeIndex;
			}

		}, null);
	}

	// Simplify type: make it a non-smt, non-sym type.
	public static Type simplify(Type t) {
		return t.accept(new TypeVisitor<Void, Type>() {

			@Override
			public Type visit(TypeVar typeVar, Void in) {
				return typeVar;
			}

			@Override
			public Type visit(AlgebraicDataType algebraicType, Void in) {
				TypeSymbol sym = algebraicType.getSymbol();
				List<Type> args = algebraicType.getTypeArgs();
				if (sym.equals(BuiltInTypeSymbol.SMT_TYPE) || sym.equals(BuiltInTypeSymbol.SYM_TYPE)) {
					return args.get(0).accept(this, in);
				}
				args = Util.map(args, t -> t.accept(this, in));
				return AlgebraicDataType.make(sym, args);
			}

			@Override
			public Type visit(OpaqueType opaqueType, Void in) {
				return opaqueType;
			}

			@Override
			public Type visit(TypeIndex typeIndex, Void in) {
				return typeIndex;
			}

		}, null);
	}

}
