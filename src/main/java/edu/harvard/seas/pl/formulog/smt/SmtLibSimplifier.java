package edu.harvard.seas.pl.formulog.smt;

import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.FORMULA_AND;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.FORMULA_LET;
import static edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol.TRUE;

import org.pcollections.HashTreePMap;
import org.pcollections.PMap;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.Expr;

public class SmtLibSimplifier {

	public SmtLibTerm simplify(SmtLibTerm term) {
		return term.visit(new TermVisitor<Void, SmtLibTerm>() {

			@Override
			public SmtLibTerm visit(Var t, Void in) {
				throw new AssertionError("impossible");
			}

			@Override
			public SmtLibTerm visit(Constructor c, Void in) {
				Term[] newArgs = Terms.map(c.getArgs(), t -> t.visit(this, in));
				if (c.getSymbol().equals(FORMULA_AND)) {
					if (isTrueTerm(newArgs[0])) {
						return (SmtLibTerm) newArgs[1];
					} else if (isTrueTerm(newArgs[1])) {
						return (SmtLibTerm) newArgs[0];
					}
				}
				if (c.getSymbol().equals(FORMULA_LET) && meetsInliningThreshold(newArgs[1])) {
					PMap<SolverVariable, SmtLibTerm> subst = HashTreePMap.singleton((SolverVariable) newArgs[0],
							(SmtLibTerm) newArgs[1]);
					return ((SmtLibTerm) newArgs[2]).substSolverTerms(subst);
				}
				return c.copyWithNewArgs(newArgs);
			}

			@Override
			public SmtLibTerm visit(Primitive<?> p, Void in) {
				return (SmtLibTerm) p;
			}

			@Override
			public SmtLibTerm visit(Expr expr, Void in) {
				throw new AssertionError("impossible");
			}

		}, null);
	}

	private static boolean isTrueTerm(Term t) {
		return t instanceof Constructor && ((Constructor) t).getSymbol().equals(TRUE);
	}

	private static boolean meetsInliningThreshold(Term t) {
		return t instanceof Primitive<?> || t instanceof SolverVariable;
	}

}
