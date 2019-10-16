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

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.ast.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;

public class TypeFinder {

	private final Set<FunctionSymbol> seenFuncs = new HashSet<>();
	private final Set<ConstructorSymbol> seenCtors = new HashSet<>();
	private final Set<TypeSymbol> types = new HashSet<>();

	public Set<TypeSymbol> getTypes() {
		return Collections.unmodifiableSet(types);
	}

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
			exploreFunction(defs.lookup(sym));
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
