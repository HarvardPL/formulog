package edu.harvard.seas.pl.formulog.ast.functions;

import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.unification.Substitution;

public final class PrimitiveConversions {
	
	private PrimitiveConversions() {
		throw new AssertionError();
	}
	
	public static final FunctionDef i32ToI64 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.i32ToI64;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 x = (I32) Terms.lookup(args[0], subst);
			return I64.make(x.getVal());
		}
		
	};
	
	public static final FunctionDef i32ToFp32 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.i32ToFp32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 x = (I32) Terms.lookup(args[0], subst);
			return FP32.make(x.getVal());
		}
		
	};
	
	public static final FunctionDef i32ToFp64 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.i32ToFp64;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I32 x = (I32) Terms.lookup(args[0], subst);
			return FP64.make(x.getVal());
		}
		
	};
	
	public static final FunctionDef i64ToI32 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.i64ToI32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 x = (I64) Terms.lookup(args[0], subst);
			return I32.make(x.getVal().intValue());
		}
		
	};
	
	public static final FunctionDef i64ToFp32 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.i64ToFp32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 x = (I64) Terms.lookup(args[0], subst);
			return FP32.make(x.getVal());
		}
		
	};
	
	public static final FunctionDef i64ToFp64 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.i64ToFp64;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			I64 x = (I64) Terms.lookup(args[0], subst);
			return FP64.make(x.getVal());
		}
		
	};
	
	public static final FunctionDef fp32ToI32 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.fp32ToI32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 x = (FP32) Terms.lookup(args[0], subst);
			return I32.make(x.getVal().intValue());
		}
		
	};
	
	public static final FunctionDef fp32ToI64 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.fp32ToI64;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 x = (FP32) Terms.lookup(args[0], subst);
			return I64.make(x.getVal().longValue());
		}
		
	};
	
	public static final FunctionDef fp32ToFp64 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.fp32ToFp64;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP32 x = (FP32) Terms.lookup(args[0], subst);
			return FP64.make(x.getVal());
		}
		
	};
	
	public static final FunctionDef fp64ToI32 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.fp64ToI32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 x = (FP64) Terms.lookup(args[0], subst);
			return I32.make(x.getVal().intValue());
		}
		
	};
	
	public static final FunctionDef fp64ToI64 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.fp64ToI64;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 x = (FP64) Terms.lookup(args[0], subst);
			return I64.make(x.getVal().longValue());
		}
		
	};
	
	public static final FunctionDef fp64ToFp32 = new FunctionDef() {

		@Override
		public Symbol getSymbol() {
			return BuiltInFunctionSymbol.fp64ToFp32;
		}

		@Override
		public Term evaluate(Term[] args, Substitution subst) throws EvaluationException {
			FP64 x = (FP64) Terms.lookup(args[0], subst);
			return FP32.make(x.getVal().floatValue());
		}
		
	};

}
