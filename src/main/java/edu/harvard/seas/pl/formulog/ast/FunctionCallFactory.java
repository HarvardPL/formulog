package edu.harvard.seas.pl.formulog.ast;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.functions.Expr;
import edu.harvard.seas.pl.formulog.ast.functions.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.Exprs.ExprVisitorExn;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.unification.EmptySubstitution;
import edu.harvard.seas.pl.formulog.unification.Substitution;
import edu.harvard.seas.pl.formulog.util.FunctorUtil;
import edu.harvard.seas.pl.formulog.util.FunctorUtil.Memoizer;
import edu.harvard.seas.pl.formulog.util.Util;

public final class FunctionCallFactory {

	private final FunctionDefManager defManager;
	private final Memoizer<FunctionCall> memo = new Memoizer<>();
	
	private static final AtomicInteger cnt = new AtomicInteger();
	private static final boolean debug = System.getProperty("callTrace") != null;

	private final Map<Symbol, Map<List<Term>, Term>> callMemo = new ConcurrentHashMap<>();

	public FunctionCallFactory(FunctionDefManager defManager) {
		this.defManager = defManager;
	}

	public FunctionCall make(Symbol sym, Term[] args) {
		if (sym.getArity() != args.length) {
			throw new IllegalArgumentException("Symbol " + sym + " has arity " + sym.getArity() + " but args "
					+ Arrays.toString(args) + " have length " + args.length);
		}
		return memo.lookupOrCreate(sym, args, () -> new FunctionCall(sym, args));
	}

	public class FunctionCall implements Functor, Expr {

		private final Symbol sym;
		private final Term[] args;
		private final boolean isGround;

		private FunctionCall(Symbol sym, Term[] args) {
			this.sym = sym;
			this.args = args;
			boolean b = true;
			for (Term t : args) {
				b &= t.isGround();
			}
			isGround = b;
			if (!sym.getSymbolType().equals(SymbolType.FUNCTION)) {
				throw new IllegalArgumentException("Cannot create a function call for a non-function symbol: " + this);
			}
		}

		@Override
		public Symbol getSymbol() {
			return sym;
		}

		@Override
		public Term[] getArgs() {
			return args;
		}

		public Term evaluate(Substitution s) throws EvaluationException {
			return evaluate(args, s);
		}

		public Term evaluate(Term[] args) throws EvaluationException {
			return evaluate(args, EmptySubstitution.INSTANCE);
		}

		// FIXME This way of implementing memoization seems expensive
		public Term evaluate(Term[] args, Substitution s) throws EvaluationException {
			Integer id = null;
			if (debug) {
				id = cnt.getAndIncrement();
				String msg = "BEGIN CALL #" + id + "\n";
				msg += "Function: " + sym + "\n";
				msg += "Arguments: " + Arrays.toString(args) + "\n";
				msg += "***\n";
				System.err.println(msg);
			}
			FunctionDef def = defManager.lookup(getSymbol());
			assert def != null;
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].applySubstitution(s).reduce(s);
			}
			Map<List<Term>, Term> m = Util.lookupOrCreate(callMemo, sym, () -> new ConcurrentHashMap<>());
			List<Term> key = Arrays.asList(newArgs);
			Term r = m.get(key);
			if (r == null) {
				r = def.evaluate(newArgs);
				Term other = m.putIfAbsent(key, r);
				if (other != null) {
					r = other;
				}
			}
			if (debug) {
				String msg = "END CALL #" + id + "\n";
				msg += "Function: " + sym + "\n";
				msg += "Arguments: " + Arrays.toString(args) + "\n";
				msg += "Result: " + r + "\n";
				msg += "***\n";
				System.err.println(msg);
			}
			return r;
		}

		@Override
		public FunctionCall copyWithNewArgs(Term[] newArgs) {
			return make(sym, newArgs);
		}

		@Override
		public boolean containsFunctionCall() {
			return true;
		}

		@Override
		public Term applySubstitution(Substitution s) {
			Term[] newArgs = Terms.map(args, t -> t.applySubstitution(s));
			return make(sym, newArgs);
		}

		@Override
		public Term reduce(Substitution s) throws EvaluationException {
			Term[] newArgs = Terms.mapExn(args, t -> t.reduce(s));
			return evaluate(newArgs, s);
		}

		@Override
		public boolean isGround() {
			return isGround;
		}

		@Override
		public String toString() {
			return FunctorUtil.toString(sym, args);
		}

		@Override
		public Term normalize(Substitution s) throws EvaluationException {
			Term[] newArgs = Terms.mapExn(args, t -> t.normalize(s));
			return evaluate(newArgs, s);
		}

		@Override
		public <I, O> O visit(ExprVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public <I, O, E extends Throwable> O visit(ExprVisitorExn<I, O, E> visitor, I in) throws E {
			return visitor.visit(this, in);
		}

	}

}
