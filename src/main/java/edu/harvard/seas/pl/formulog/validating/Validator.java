package edu.harvard.seas.pl.formulog.validating;

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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.RelationProperties;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInPredicateSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.unification.SimpleSubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.UnionFind;
import edu.harvard.seas.pl.formulog.util.Util;

public class Validator {

	private final Program prog;
	private ValidProgram vprog;
	private final Map<Symbol, Set<Rule>> rules = new HashMap<>();
	private final Map<Symbol, Set<Atom>> facts = new HashMap<>();

	public Validator(Program prog) {
		this.prog = prog;
	}

	public synchronized ValidProgram validate() throws InvalidProgramException {
		if (vprog == null) {
			validateFacts();
			validateRules();
			validateFunctionDefs();
			List<Stratum> strata = (new Stratifier(prog)).stratify();
			vprog = new ValidProgramImpl(strata);
		}
		return vprog;
	}

	private Atom normalizeFact(Atom fact) throws InvalidProgramException {
		try {
			return Atoms.normalize(fact);
		} catch (EvaluationException e) {
			throw new InvalidProgramException(
					"Fact contains an expression that cannot be normalized: " + fact + "\n" + e);
		}
	}

	private void normalizeAggregateInit(Symbol sym) throws InvalidProgramException {
		try {
			RelationProperties props = prog.getRelationProperties(sym);
			if (props.isAggregated()) {
				Symbol funcSym = props.getAggFuncSymbol();
				Term init = props.getAggFuncInit();
				props.aggregate(funcSym, init.normalize(new SimpleSubstitution()));
			}
		} catch (EvaluationException e) {
			throw new InvalidProgramException(
					"Could not normalize aggregate initial value for relation " + sym + "\n" + e.getMessage());
		}
	}

	private void validateFacts() throws InvalidProgramException {
		for (Symbol sym : prog.getFactSymbols()) {
			normalizeAggregateInit(sym);
			Set<Atom> s = new HashSet<>();
			for (Atom fact : prog.getFacts(sym)) {
				if (!sym.getSymbolType().isEDBSymbol()) {
					throw new InvalidProgramException("Cannot define facts for non-EDB symbol " + sym);
				}
				if (!Atoms.varSet(fact).isEmpty()) {
					throw new InvalidProgramException("Every fact must be ground: " + fact);
				}
				s.add(normalizeFact(fact));
			}
			facts.put(sym, s);
		}
	}

	private void validateRules() throws InvalidProgramException {
		for (Symbol sym : prog.getRuleSymbols()) {
			normalizeAggregateInit(sym);
			Set<Rule> s = new HashSet<>();
			for (Rule r : prog.getRules(sym)) {
				try {
					r = rewriteRule(r);
					Set<Var> vars = validateHead(r);
					validateBody(r.getBody(), vars);
					s.add(simplifyRule(r));
				} catch (InvalidProgramException e) {
					throw new InvalidProgramException("Invalid rule (" + e.getMessage() + "):\n" + r);
				}
			}
			rules.put(sym, s);
		}
	}

	private static Rule simplifyRule(Rule r) {
		Atom newHead = simplifyAtom(r.getHead());
		List<Atom> newBody = new ArrayList<>();
		for (Atom a : r.getBody()) {
			newBody.add(simplifyAtom(a));
		}
		return BasicRule.get(newHead, newBody);
	}

	private static Atom simplifyAtom(Atom a) {
		Term[] args = a.getArgs();
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].visit(termSimplifier, null);
		}
		return Atoms.get(a.getSymbol(), newArgs, a.isNegated());
	}

	private static final TermVisitor<Void, Term> termSimplifier = new TermVisitor<Void, Term>() {

		@Override
		public Term visit(Var t, Void in) {
			return t;
		}

		@Override
		public Term visit(Constructor c, Void in) {
			Term[] args = c.getArgs();
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].visit(this, in);
			}
			return c.copyWithNewArgs(newArgs);
		}

		@Override
		public Term visit(Primitive<?> p, Void in) {
			return p;
		}

		@Override
		public Term visit(Expr expr, Void in) {
			return expr.visit(exprSimplifier, in);
		}

	};

	private static final ExprVisitor<Void, Term> exprSimplifier = new ExprVisitor<Void, Term>() {

		@Override
		public Term visit(MatchExpr matchExpr, Void in) {
			Term matchee = matchExpr.getMatchee().visit(termSimplifier, in);
			List<MatchClause> clauses = new ArrayList<>();
			for (MatchClause cl : matchExpr.getClauses()) {
				Term lhs = cl.getLhs().visit(termSimplifier, in);
				Term rhs = cl.getRhs().visit(termSimplifier, in);
				clauses.add(MatchClause.make(lhs, rhs));
			}
			return MatchExpr.make(matchee, clauses);
		}

		@Override
		public Term visit(FunctionCall f, Void in) {
			Symbol sym = f.getSymbol();
			if (sym.equals(BuiltInFunctionSymbol.ENTER_FORMULA) || sym.equals(BuiltInFunctionSymbol.EXIT_FORMULA)) {
				return f.getArgs()[0].visit(termSimplifier, in);
			}
			Term[] args = f.getArgs();
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].visit(termSimplifier, in);
			}
			return f.copyWithNewArgs(newArgs);
		}

	};

	private static TermVisitor<List<Atom>, Term> funcRemover = new TermVisitor<List<Atom>, Term>() {

		@Override
		public Term visit(Var x, List<Atom> in) {
			return x;
		}

		@Override
		public Term visit(Constructor c, List<Atom> in) {
			Term[] args = c.getArgs();
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].visit(this, in);
			}
			Var x = Var.getFresh(false);
			Atom eq = makeUnifier(x, c.copyWithNewArgs(newArgs), false);
			in.add(eq);
			return x;
		}

		@Override
		public Term visit(Primitive<?> p, List<Atom> in) {
			Var x = Var.getFresh(false);
			Atom eq = makeUnifier(x, p, false);
			in.add(eq);
			return x;
		}

		@Override
		public Term visit(Expr expr, List<Atom> in) {
			Var x = Var.getFresh(false);
			Atom eq = makeUnifier(x, expr, false);
			in.add(eq);
			return x;
		}

	};

	private static UnifyAtom makeUnifier(Term t1, Term t2, boolean neg) {
		return (UnifyAtom) Atoms.get(BuiltInPredicateSymbol.UNIFY, new Term[] { t1, t2 }, neg);
	}

	private Atom removeFuncs(Atom a, List<Atom> acc) {
		if (a instanceof UnifyAtom) {
			return a;
		}
		Term[] args = a.getArgs();
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].visit(funcRemover, acc);
		}
		return Atoms.get(a.getSymbol(), newArgs, a.isNegated());
	}

	// Remove function calls
	private Rule rewriteRule(Rule r) throws InvalidProgramException {
		r = removeNestedFuncs(r);
		r = simplifyUnifications(r);
		return removeVarEqualities(r);
	}

	private Rule removeNestedFuncs(Rule r) {
		List<Atom> newBody = new ArrayList<>();
		for (Atom a : r.getBody()) {
			newBody.add(removeFuncs(a, newBody));
		}
		Atom newHead = removeFuncs(r.getHead(), newBody);
		return BasicRule.get(newHead, newBody);
	}

	private Rule simplifyUnifications(Rule r) throws InvalidProgramException {
		List<Atom> newBody = new ArrayList<>();
		for (Atom a : r.getBody()) {
			if (a instanceof UnifyAtom) {
				UnifyAtom u = (UnifyAtom) a;
				if (a.isNegated()) {
					simplifyNegatedUnification(u, newBody);
				} else {
					simplifyPositiveUnification(u, newBody);
				}
			} else {
				newBody.add(a);
			}
		}
		if (newBody.isEmpty()) {
			newBody.add(Atoms.trueAtom);
		}
		return BasicRule.get(r.getHead(), newBody);
	}

	private void simplifyNegatedUnification(UnifyAtom a, List<Atom> acc) {
		Term arg1 = a.getArgs()[0];
		Term arg2 = a.getArgs()[1];
		if (arg1 instanceof Constructor && arg2 instanceof Constructor) {
			Constructor c1 = (Constructor) arg1;
			Constructor c2 = (Constructor) arg2;
			Symbol sym = c1.getSymbol();
			if (!sym.equals(c2.getSymbol())) {
				return;
			}
			Term[] args1 = replaceTermsWithVars(c1.getArgs(), acc);
			Term[] args2 = replaceTermsWithVars(c2.getArgs(), acc);
			acc.add(makeUnifier(Constructors.make(sym, args1), Constructors.make(sym, args2), true));
		} else {
			acc.add(a);
		}
	}

	private Term[] replaceTermsWithVars(Term[] args, List<Atom> acc) {
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			Var x = Var.getFresh(false);
			newArgs[i] = x;
			acc.add(makeUnifier(x, args[i], false));
		}
		return args;
	}

	private void simplifyPositiveUnification(UnifyAtom a, List<Atom> acc) throws InvalidProgramException {
		Term arg1 = a.getArgs()[0];
		Term arg2 = a.getArgs()[1];
		if (arg1 instanceof Constructor && arg2 instanceof Constructor) {
			Constructor c1 = (Constructor) arg1;
			Constructor c2 = (Constructor) arg2;
			if (!c1.getSymbol().equals(c2.getSymbol())) {
				throw new InvalidProgramException("Contains unsatisfiable unification premise: " + a);
			}
			Term[] args1 = c1.getArgs();
			Term[] args2 = c2.getArgs();
			for (int i = 0; i < args1.length; ++i) {
				simplifyPositiveUnification(makeUnifier(args1[i], args2[i], false), acc);
			}
		} else {
			acc.add(a);
		}
	}

	private Rule removeVarEqualities(Rule r) {
		List<Atom> body = Util.iterableToList(r.getBody());
		Substitution subst = removeVarEqualities(body);
		List<Atom> newBody = new ArrayList<>();
		for (Atom a : body) {
			newBody.add(Atoms.applySubstitution(a, subst));
		}
		Atom newHead = Atoms.applySubstitution(r.getHead(), subst);
		return BasicRule.get(newHead, newBody);
	}

	private Substitution removeVarEqualities(List<Atom> atoms) {
		List<Atom> newAtoms = new ArrayList<>();
		UnionFind<Var> uf = new UnionFind<>();
		Substitution subst = new Substitution() {

			@Override
			public void put(Var v, Term t) {
				throw new AssertionError("impossible");
			}

			@Override
			public Term get(Var v) {
				return uf.find(v);
			}

			@Override
			public boolean containsKey(Var v) {
				return uf.contains(v);
			}

			@Override
			public Iterable<Var> iterateKeys() {
				List<Var> vars = new ArrayList<>();
				for (Term t : uf.members()) {
					if (t instanceof Var) {
						vars.add((Var) t);
					}
				}
				return vars;
			}

		};
		for (Atom a : atoms) {
			Term[] args = a.getArgs();
			if (a instanceof UnifyAtom && !a.isNegated()) {
				if (args[0] instanceof Var && args[1] instanceof Var) {
					Var x = (Var) args[0];
					Var y = (Var) args[1];
					uf.add(x);
					uf.add(y);
					uf.union(x, y);
					continue;
				}
			}
			newAtoms.add(a);
		}
		atoms.clear();
		atoms.addAll(newAtoms);
		return subst;
	}

	private Set<Var> validateHead(Rule r) throws InvalidProgramException {
		Atom hd = r.getHead();
		if (hd.isNegated()) {
			throw new InvalidProgramException("Cannot define a rule with a negated head\n" + r);
		}
		Symbol sym = hd.getSymbol();
		if (!sym.getSymbolType().isIDBSymbol()) {
			throw new InvalidProgramException("Cannot define rules for non-IDB symbol " + sym);
		}
		return Atoms.varSet(hd);
	}

	private void validateBody(Iterable<Atom> body, Set<Var> unboundVars) throws InvalidProgramException {
		for (Atom a : body) {
			unboundVars.addAll(Atoms.varSet(a));
			validateTerms(a.getArgs());
		}
		Set<Var> boundVars = new HashSet<>();
		boolean changed;
		do {
			changed = false;
			for (Atom a : body) {
				if (Unification.canBindVars(a, boundVars)) {
					changed |= boundVars.addAll(Atoms.varSet(a));
				}
			}
		} while (changed);
		unboundVars.removeAll(boundVars);
		if (!unboundVars.isEmpty()) {
			StringBuilder sb = new StringBuilder("There are unbound variables: ");
			for (Iterator<Var> it = unboundVars.iterator(); it.hasNext();) {
				sb.append("\"" + it.next() + "\"");
				if (it.hasNext()) {
					sb.append(", ");
				}
			}
			throw new InvalidProgramException(sb.toString());
		}
	}

	private static final TermVisitorExn<Void, Void, InvalidProgramException> termValidator = new TermVisitorExn<Void, Void, InvalidProgramException>() {

		@Override
		public Void visit(Var x, Void in) throws InvalidProgramException {
			return null;
		}

		@Override
		public Void visit(Constructor c, Void in) throws InvalidProgramException {
			for (Term arg : c.getArgs()) {
				arg.visit(this, in);
			}
			return null;
		}

		@Override
		public Void visit(Primitive<?> p, Void in) throws InvalidProgramException {
			return null;
		}

		@Override
		public Void visit(Expr e, Void in) throws InvalidProgramException {
			e.visit(exprValidator, in);
			return null;
		}

	};

	private static final ExprVisitorExn<Void, Void, InvalidProgramException> exprValidator = new ExprVisitorExn<Void, Void, InvalidProgramException>() {

		@Override
		public Void visit(MatchExpr matchExpr, Void in) throws InvalidProgramException {
			validateTerm(matchExpr.getMatchee());
			for (MatchClause cl : matchExpr.getClauses()) {
				Term lhs = cl.getLhs();
				validateTerm(lhs);
				if (lhs.containsFunctionCall()) {
					throw new InvalidProgramException("Cannot have a match pattern with a reducible term: " + lhs);
				}
				validateTerm(cl.getRhs());
			}
			return null;
		}

		@Override
		public Void visit(FunctionCall funcCall, Void in) throws InvalidProgramException {
			for (Term arg : funcCall.getArgs()) {
				arg.visit(termValidator, in);
			}
			return null;
		}

	};

	private static void validateTerm(Term term) throws InvalidProgramException {
		term.visit(termValidator, null);
	}

	private static void validateTerms(Term[] terms) throws InvalidProgramException {
		for (Term t : terms) {
			validateTerm(t);
		}
	}

	private void validateFunctionDefs() throws InvalidProgramException {
		for (Symbol sym : prog.getFunctionSymbols()) {
			FunctionDef def = prog.getDef(sym);
			if (def instanceof CustomFunctionDef) {
				CustomFunctionDef cdef = (CustomFunctionDef) def;
				try {
					Set<Var> boundVars = validateFunctionParams(cdef.getParams());
					validateFunctionBody(cdef.getBody(), boundVars);
				} catch (InvalidProgramException e) {
					throw new InvalidProgramException("Invalid function definition (" + e.getMessage() + "): " + sym + "\n" + cdef.getBody());
				}
			}
		}
	}

	private Set<Var> validateFunctionParams(Var[] params) throws InvalidProgramException {
		Set<Var> vars = new HashSet<>();
		for (Var param : params) {
			if (!vars.add(param)) {
				throw new InvalidProgramException(
						"Cannout use the same variable multiple times in the argument to a function definition");
			}
		}
		return vars;
	}

	private void validateFunctionBody(Term body, Set<Var> boundVars) throws InvalidProgramException {
		validateTerm(body);
		Set<Var> freeVars = Terms.varSet(body);
		freeVars.removeAll(boundVars);
		if (!freeVars.isEmpty()) {
			StringBuilder sb = new StringBuilder();
			for (Iterator<Var> it = freeVars.iterator(); it.hasNext();) {
				sb.append("\"" + it.next() + "\"");
				if (it.hasNext()) {
					sb.append(", ");
				}
			}
			throw new InvalidProgramException("Unbound variables: " + sb.toString());
		}
	}

	private class ValidProgramImpl implements ValidProgram {

		private final Map<Symbol, Integer> ranks;
		private final List<Stratum> strata;

		private ValidProgramImpl(List<Stratum> strata) {
			this.strata = strata;
			ranks = new HashMap<>();
			int i = 0;
			for (Stratum stratum : strata) {
				for (Symbol sym : stratum.getPredicateSyms()) {
					assert !ranks.containsKey(sym);
					ranks.put(sym, i);
				}
				++i;
			}
		}

		@Override
		public Set<Symbol> getFunctionSymbols() {
			return prog.getFunctionSymbols();
		}

		@Override
		public Set<Symbol> getFactSymbols() {
			return facts.keySet();
		}

		@Override
		public Set<Symbol> getRuleSymbols() {
			return prog.getRuleSymbols();
		}

		@Override
		public FunctionDef getDef(Symbol sym) {
			return prog.getDef(sym);
		}

		@Override
		public Set<Atom> getFacts(Symbol sym) {
			assert sym.getSymbolType().isEDBSymbol();
			return facts.get(sym);
		}

		@Override
		public Set<Rule> getRules(Symbol sym) {
			assert sym.getSymbolType().isIDBSymbol();
			return rules.get(sym);
		}

		@Override
		public int getStratumRank(Symbol sym) {
			if (sym.getSymbolType().isEDBSymbol()) {
				throw new IllegalArgumentException("EDB predicates (such as " + sym + ") do not belong to a stratum");
			}
			return ranks.get(sym);
		}

		@Override
		public Stratum getStratum(int rank) {
			if (rank < 0 || rank >= strata.size()) {
				throw new IllegalArgumentException(
						"Rank of " + rank + " out of required range of [0, " + strata.size() + ")");
			}
			return strata.get(rank);
		}

		@Override
		public int getNumberOfStrata() {
			return strata.size();
		}

		@Override
		public SymbolManager getSymbolManager() {
			return prog.getSymbolManager();
		}

		@Override
		public RelationProperties getRelationProperties(Symbol sym) {
			return prog.getRelationProperties(sym);
		}

		@Override
		public boolean hasQuery() {
			return prog.hasQuery();
		}

		@Override
		public NormalAtom getQuery() {
			return prog.getQuery();
		}

		@Override
		public FunctionCallFactory getFunctionCallFactory() {
			return prog.getFunctionCallFactory();
		}

	}
}
