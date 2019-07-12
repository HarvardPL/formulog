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
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.RelationProperties;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.AtomVisitor;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class TypeChecker {

	private final Program prog;

	public TypeChecker(Program prog) {
		this.prog = prog;
	}

	public WellTypedProgram typeCheck() throws TypeException {
		Map<Symbol, Set<Atom>> newFacts = typeCheckFacts();
		Map<Symbol, FunctionDef> newFuncs = typeCheckFunctions();
		FunctionDefManager dm = prog.getFunctionCallFactory().getDefManager();
		for (FunctionDef func : newFuncs.values()) {
			dm.reregister(func);
		}
		Map<Symbol, RelationProperties> newProps = typeCheckRelations();
		Map<Symbol, Set<Rule>> newRules = typeCheckRules();
		Atom newQuery = typeCheckQuery();
		return new WellTypedProgram() {

			@Override
			public Set<Symbol> getFunctionSymbols() {
				return newFuncs.keySet();
			}

			@Override
			public Set<Symbol> getFactSymbols() {
				return Collections.unmodifiableSet(newFacts.keySet());
			}

			@Override
			public Set<Symbol> getRuleSymbols() {
				return Collections.unmodifiableSet(newRules.keySet());
			}

			@Override
			public FunctionDef getDef(Symbol sym) {
				return newFuncs.get(sym);
			}

			@Override
			public Set<Atom> getFacts(Symbol sym) {
				assert sym.getSymbolType().isEDBSymbol();
				return Util.lookupOrCreate(newFacts, sym, () -> Collections.emptySet());
			}

			@Override
			public Set<Rule> getRules(Symbol sym) {
				assert sym.getSymbolType().isIDBSymbol();
				return Util.lookupOrCreate(newRules, sym, () -> Collections.emptySet());
			}

			@Override
			public SymbolManager getSymbolManager() {
				return prog.getSymbolManager();
			}

			@Override
			public RelationProperties getRelationProperties(Symbol sym) {
				assert sym.getSymbolType().isRelationSym();
				return Util.lookupOrCreate(newProps, sym, () -> new RelationProperties(sym));
			}

			@Override
			public boolean hasQuery() {
				return newQuery != null;
			}

			@Override
			public NormalAtom getQuery() {
				return (NormalAtom) newQuery;
			}

			@Override
			public FunctionCallFactory getFunctionCallFactory() {
				return prog.getFunctionCallFactory();
			}

		};
	}

	private Map<Symbol, RelationProperties> typeCheckRelations() throws TypeException {
		Map<Symbol, RelationProperties> props = new HashMap<>();
		typeCheckRelations(prog.getFactSymbols(), props);
		typeCheckRelations(prog.getRuleSymbols(), props);
		return props;
	}

	private void typeCheckRelations(Set<Symbol> syms, Map<Symbol, RelationProperties> props) throws TypeException {
		for (Symbol sym : syms) {
			props.put(sym, typeCheckRelation(sym));
		}
	}

	private RelationProperties typeCheckRelation(Symbol sym) throws TypeException {
		RelationProperties props = new RelationProperties(prog.getRelationProperties(sym));
		if (props.isAggregated()) {
			FunctorType ft = (FunctorType) sym.getCompileTimeType();
			List<Type> argTypes = ft.getArgTypes();
			Type aggType = argTypes.get(argTypes.size() - 1);
			Term init = typeCheckAggregateUnit(sym, props.getAggFuncInit(), aggType);
			typeCheckAggregateFunction(sym, props.getAggFuncSymbol(), aggType);
			props.aggregate(props.getAggFuncSymbol(), init);
		}
		return props;
	}

	private Term typeCheckAggregateUnit(Symbol relSym, Term unit, Type aggType) throws TypeException {
		try {
			TypeCheckerContext ctx = new TypeCheckerContext();
			return ctx.typeCheckTerm(unit, aggType);
		} catch (TypeException e) {
			throw new TypeException(
					"Error with aggregate unit term " + unit + " for relation " + relSym + "\n" + e.getMessage());
		}
	}

	private void typeCheckAggregateFunction(Symbol relSym, Symbol funcSym, Type aggType) throws TypeException {
		try {
			if (funcSym.getArity() != 2) {
				throw new TypeException("Function " + funcSym + " is not binary");
			}
			FunctorType funcType = (FunctorType) funcSym.getCompileTimeType();
			List<Type> actualTypes = new ArrayList<>(funcType.getArgTypes());
			actualTypes.add(funcType.getRetType());
			List<Type> requiredTypes = Arrays.asList(aggType, aggType, aggType);
			TypeCheckerContext ctx = new TypeCheckerContext();
			ctx.checkUnifiability(actualTypes, requiredTypes);
		} catch (TypeException e) {
			throw new TypeException(
					"Error with aggregate function " + funcSym + " for relation " + relSym + "\n" + e.getMessage());
		}
	}

	private Atom typeCheckQuery() throws TypeException {
		if (prog.hasQuery()) {
			TypeCheckerContext ctx = new TypeCheckerContext();
			return ctx.typeCheckQuery(prog.getQuery());
		}
		return null;
	}

	private Map<Symbol, Set<Atom>> typeCheckFacts() throws TypeException {
		// Can use same type checker context for all, since there should be neither
		// program variables (in a fact) or type variables (in a relation type).
		// Addendum: there can be program variables (in type index positions),
		// but they should be unique.
		Map<Symbol, Set<Atom>> m = new HashMap<>();
		TypeCheckerContext ctx = new TypeCheckerContext();
		for (Symbol sym : prog.getFactSymbols()) {
			Set<Atom> s = new HashSet<>();
			for (Atom a : prog.getFacts(sym)) {
				s.add(ctx.typeCheckFact(a));
			}
			m.put(sym, s);
		}
		return m;
	}

	private Map<Symbol, Set<Rule>> typeCheckRules() throws TypeException {
		Map<Symbol, Set<Rule>> m = new HashMap<>();
		for (Symbol sym : prog.getRuleSymbols()) {
			Set<Rule> s = new HashSet<>();
			for (Rule r : prog.getRules(sym)) {
				TypeCheckerContext ctx = new TypeCheckerContext();
				s.add(ctx.typeCheckRule(r));
			}
			m.put(sym, s);
		}
		return m;
	}

	private Map<Symbol, FunctionDef> typeCheckFunctions() throws TypeException {
		Map<Symbol, FunctionDef> m = new HashMap<>();
		for (Symbol sym : prog.getFunctionSymbols()) {
			FunctionDef def = prog.getDef(sym);
			if (def instanceof CustomFunctionDef) {
				TypeCheckerContext ctx = new TypeCheckerContext();
				def = ctx.typeCheckFunction((CustomFunctionDef) def);
			}
			m.put(sym, def);
		}
		return m;
	}

	private class TypeCheckerContext {

		private final Deque<Pair<Type, Type>> constraints = new ArrayDeque<>();
		private final Deque<Pair<Type, Type>> formulaConstraints = new ArrayDeque<>();
		private final Map<TypeVar, Type> typeVars = new HashMap<>();
		private String error;

		public Atom typeCheckFact(Atom a) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(a, subst);
			if (!checkConstraints()) {
				throw new TypeException("Type error in fact: " + a + "\n" + error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return Atoms.applySubstitution(a, m);
		}

		public Atom typeCheckQuery(Atom q) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(q, subst);
			if (!checkConstraints()) {
				throw new TypeException("Type error in query: " + q + "\n" + error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return Atoms.applySubstitution(q, m);
		}

		public Rule typeCheckRule(Rule r) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			processAtoms(r.getBody(), subst);
			genConstraints(r.getHead(), subst);
			if (!checkConstraints()) {
				String msg = "Type error in rule:\n";
				msg += r + "\n";
				msg += error;
				throw new TypeException(msg);
			}
			Substitution m = makeIndexSubstitution(subst);
			Atom newHead = Atoms.applySubstitution(r.getHead(), m);
			List<Atom> newBody = new ArrayList<>();
			for (Atom a : r.getBody()) {
				newBody.add(Atoms.applySubstitution(a, m));
			}
			return BasicRule.get(newHead, newBody);
		}

		private Substitution makeIndexSubstitution(Map<Var, Type> subst) {
			Substitution m = new SimpleSubstitution();
			for (Map.Entry<Var, Type> e : subst.entrySet()) {
				Var x = e.getKey();
				Type t = lookupType(e.getValue());
				if (t instanceof TypeIndex) {
					int idx = ((TypeIndex) t).getIndex();
					Symbol csym = prog.getSymbolManager().lookupIndexConstructorSymbol(idx);
					Term c = Constructors.make(csym, Terms.singletonArray(I32.make(idx)));
					m.put(x, c);
				}
			}
			return m;
		}
		
		public CustomFunctionDef typeCheckFunction(CustomFunctionDef functionDef) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(functionDef, subst);
			if (!checkConstraints()) {
				throw new TypeException("Type error in function: " + functionDef.getSymbol() + "\n" + error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return CustomFunctionDef.get(functionDef.getSymbol(), functionDef.getParams(), functionDef.getBody().applySubstitution(m));
		}

		public Term typeCheckTerm(Term t, Type type) throws TypeException {
			Map<Var, Type> subst = new HashMap<>();
			genConstraints(t, type, subst, false);
			if (!checkConstraints()) {
				throw new TypeException(error);
			}
			Substitution m = makeIndexSubstitution(subst);
			return t.applySubstitution(m);
		}

		public void checkUnifiability(List<Type> xs, List<Type> ys) throws TypeException {
			assert xs.size() == ys.size();
			for (Iterator<Type> it1 = xs.iterator(), it2 = ys.iterator(); it1.hasNext();) {
				addConstraint(it1.next(), it2.next(), false);
			}
			if (!checkConstraints()) {
				throw new TypeException(error);
			}
		}

		private void processAtoms(Iterable<Atom> atoms, Map<Var, Type> subst) {
			for (Atom a : atoms) {
				genConstraints(a, subst);
			}
		}

		private void genConstraints(Atom a, Map<Var, Type> subst) {
			a.visit(new AtomVisitor<Void, Void>() {

				@Override
				public Void visit(NormalAtom normalAtom, Void in) {
					FunctorType ftype = (FunctorType) normalAtom.getSymbol().getCompileTimeType().freshen();
					Term[] args = normalAtom.getArgs();
					assert ftype.getArgTypes().size() == args.length;
					int i = 0;
					for (Type type : ftype.getArgTypes()) {
						genConstraints(args[i], type, subst, false);
						++i;
					}
					return null;
				}

				@Override
				public Void visit(UnifyAtom unifyAtom, Void in) {
					TypeVar var = TypeVar.fresh();
					Term[] args = unifyAtom.getArgs();
					genConstraints(args[0], var, subst, false);
					genConstraints(args[1], var, subst, false);
					return null;
				}

			}, null);
		}

		private void genConstraints(CustomFunctionDef def, Map<Var,Type> subst) {
			Symbol sym = def.getSymbol();
			FunctorType scheme = (FunctorType) sym.getCompileTimeType().freshen();
			Map<TypeVar, OpaqueType> opaqueTypes = new HashMap<>();
			List<Type> argTypes = scheme.getArgTypes();
			for (Type t : argTypes) {
				if (t instanceof TypeVar) {
					addConstraint(t, Util.lookupOrCreate(opaqueTypes, (TypeVar) t, () -> OpaqueType.get()), false);
				}
			}
			Type r = scheme.getRetType();
			if (r instanceof TypeVar) {
				addConstraint(r, Util.lookupOrCreate(opaqueTypes, (TypeVar) r, () -> OpaqueType.get()), false);
			}
			Var[] params = def.getParams();
			for (int i = 0; i < params.length; ++i) {
				subst.put(params[i], argTypes.get(i));
			}
			genConstraints(def.getBody(), r, subst, false);
		}

		private void genConstraintsForExpr(Expr e, Type exprType, Map<Var, Type> varTypes, boolean allowSubtype) {
			e.visit(new ExprVisitor<Void, Void>() {

				@Override
				public Void visit(MatchExpr matchExpr, Void in) {
					assert !allowSubtype;
					TypeVar guardType = TypeVar.fresh();
					Term guard = matchExpr.getMatchee();
					genConstraints(guard, guardType, varTypes, allowSubtype);
					for (MatchClause cl : matchExpr.getClauses()) {
						genConstraints(cl.getLhs(), guardType, varTypes, allowSubtype);
						genConstraints(cl.getRhs(), exprType, varTypes, allowSubtype);
					}
					return null;
//					assert !allowSubtype;
//					TypeVar guardType = TypeVar.fresh();
//					Term guard = matchExpr.getMatchee();
//					// We do not need to make a copy of varTypes here. We might worry that a
//					// variable is bound in the guard expression and then that binding leaks into
//					// this scope. However, variables are only bound in match patterns, and a fresh
//					// var map is created for each match pattern.
//					genConstraints(guard, guardType, varTypes, allowSubtype);
//					for (MatchClause cl : matchExpr.getClauses()) {
//						// Use a fresh var map when type checking a pattern (because of variable
//						// shadowing).
//						Map<Var, Type> newVarTypes = new HashMap<>();
//						genConstraints(cl.getLhs(), guardType, newVarTypes, allowSubtype);
//						// However, still need to propagate any variables that are not re-bound in
//						// pattern.
//						for (Map.Entry<Var, Type> e : varTypes.entrySet()) {
//							newVarTypes.putIfAbsent(e.getKey(), e.getValue());
//						}
//						genConstraints(cl.getRhs(), exprType, newVarTypes, allowSubtype);
//					}
//					return null;
				}

				@Override
				public Void visit(FunctionCall funcCall, Void in) {
					genConstraintsForFunctionCall(funcCall, exprType, varTypes, allowSubtype);
					return null;
				}

			}, null);
		}

		private void addConstraint(Type t1, Type t2, boolean inFormula) {
			Pair<Type, Type> constraint = new Pair<>(t1, t2);
			if (inFormula) {
				formulaConstraints.add(constraint);
			} else {
				constraints.add(constraint);
			}
		}

		private void genConstraints(Term t, Type ttype, Map<Var, Type> subst, boolean allowSubtype) {
			t.visit(new TermVisitor<Void, Void>() {

				@Override
				public Void visit(Var t, Void in) {
					genConstraintsForVar(t, ttype, subst, allowSubtype);
					return null;
				}

				@Override
				public Void visit(Constructor t, Void in) {
					genConstraintsForConstructor(t, ttype, subst, allowSubtype);
					return null;
				}

				@Override
				public Void visit(Primitive<?> prim, Void in) {
					genConstraintsForPrimitive(prim, ttype, allowSubtype);
					return null;
				}

				@Override
				public Void visit(Expr expr, Void in) {
					genConstraintsForExpr(expr, ttype, subst, allowSubtype);
					return null;
				}

			}, null);
		}

		private void genConstraintsForVar(Var t, Type ttype, Map<Var, Type> subst, boolean inFormula) {
			Type s = Util.lookupOrCreate(subst, t, () -> TypeVar.fresh());
			addConstraint(s, ttype, inFormula);
		}

		private void genConstraintsForPrimitive(Primitive<?> t, Type ttype, boolean inFormula) {
			addConstraint(ttype, t.getType(), inFormula);
		}

		private void genConstraintsForConstructor(Constructor t, Type ttype, Map<Var, Type> subst,
				boolean allowSubtype) {
			Symbol cnstrSym = t.getSymbol();
			FunctorType cnstrType = (FunctorType) cnstrSym.getCompileTimeType().freshen();
			Term[] args = t.getArgs();
			List<Type> argTypes = cnstrType.getArgTypes();
			for (int i = 0; i < args.length; ++i) {
				Type argType = argTypes.get(i);
				genConstraints(args[i], argType, subst, allowSubtype);
			}
			addConstraint(cnstrType.getRetType(), ttype, allowSubtype);
		}

		private void genConstraintsForFunctionCall(FunctionCall function, Type ttype, Map<Var, Type> subst,
				boolean inFormula) {
			boolean wasInFormula = inFormula;
			if (function.getSymbol().equals(BuiltInFunctionSymbol.ENTER_FORMULA)) {
				assert !wasInFormula;
				inFormula = true;
			}
			if (function.getSymbol().equals(BuiltInFunctionSymbol.EXIT_FORMULA)) {
				inFormula = false;
			}
			FunctorType funType = (FunctorType) function.getSymbol().getCompileTimeType().freshen();
			Term[] args = function.getArgs();
			List<Type> argTypes = funType.getArgTypes();
			for (int i = 0; i < args.length; ++i) {
				genConstraints(args[i], argTypes.get(i), subst, inFormula);
			}
			addConstraint(funType.getRetType(), ttype, wasInFormula);
		}

		private boolean checkConstraints() {
			Set<Type> typesInFormulae = new HashSet<>();
			for (Pair<Type, Type> p : formulaConstraints) {
				typesInFormulae.add(p.fst());
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
			return lookupType(ty).visit(new TypeVisitor<Void, Boolean>() {

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
						if (!arg.visit(this, in)) {
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
			Deque<Pair<Type, Type>> q = inFormulaContext ? formulaConstraints : constraints;
			while (!q.isEmpty()) {
				Pair<Type, Type> pair = q.pop();
				Type type1 = lookupType(pair.fst());
				Type type2 = lookupType(pair.snd());
				if (inFormulaContext) {
					type1 = simplify(type1);
					type2 = simplify(type2);
				}
				if (type1.isVar() || type2.isVar()) {
					if (!handleVars(type1, type2)) {
						return false;
					}
				} else if (!unify(type1, type2)) {
					error = "Cannot unify " + type1 + " and " + type2;
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

		private boolean unify(Type type1, Type type2) {
			return type1.visit(new TypeVisitor<Type, Boolean>() {

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
						addConstraint(args1.get(i), args2.get(i), false);
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
		return t.visit(new TypeVisitor<Void, Type>() {

			@Override
			public Type visit(TypeVar typeVar, Void in) {
				if (subst.containsKey(typeVar)) {
					return subst.get(typeVar).visit(this, in);
				}
				return typeVar;
			}

			@Override
			public Type visit(AlgebraicDataType algebraicType, Void in) {
				List<Type> args = Util.map(algebraicType.getTypeArgs(), t -> t.visit(this, in));
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

	// Simplify type: make it a non-expr, non-sym type.
	public static Type simplify(Type t) {
		return t.visit(new TypeVisitor<Void, Type>() {

			@Override
			public Type visit(TypeVar typeVar, Void in) {
				return typeVar;
			}

			@Override
			public Type visit(AlgebraicDataType algebraicType, Void in) {
				Symbol sym = algebraicType.getSymbol();
				List<Type> args = algebraicType.getTypeArgs();
				if (sym.equals(BuiltInTypeSymbol.SMT_TYPE) || sym.equals(BuiltInTypeSymbol.SYM_TYPE)) {
					return args.get(0).visit(this, in);
				}
				args = Util.map(args, t -> t.visit(this, in));
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
