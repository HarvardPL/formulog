package edu.harvard.seas.pl.formulog.ast.functions;

import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef.MatchExpr;

public final class Exprs {

	private Exprs() {
		throw new AssertionError("impossible");
	}
	

	public static interface ExprVisitor<I, O> {

		O visit(MatchExpr matchExpr, I in);
		
		O visit(FunctionCall funcCall, I in);

	}

	public static interface ExprVisitorExn<I, O, E extends Throwable> {

		O visit(MatchExpr matchExpr, I in) throws E;
		
		O visit(FunctionCall funcCall, I in) throws E;

	}
	
}
