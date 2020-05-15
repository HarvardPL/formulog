package formulog.ast;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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



import java.util.Arrays;
import java.util.Map;
import java.util.Set;

import formulog.ast.Exprs.ExprVisitor;
import formulog.ast.Exprs.ExprVisitorExn;
import formulog.ast.FunctionCallFactory.FunctionCall;
import formulog.eval.EvaluationException;
import formulog.functions.FunctionDef;
import formulog.symbols.BuiltInConstructorSymbol;
import formulog.symbols.FunctionSymbol;
import formulog.unification.Substitution;

public class Fold implements Expr {

	private final FunctionSymbol f;
	private final Term[] args;
	private final FunctionCallFactory funCalls;
	private Boolean isGround;

	private Fold(FunctionSymbol f, Term[] args, FunctionCallFactory funCalls) {
		this.f = f;
		this.args = args;
		this.funCalls = funCalls;
		if (f.getArity() != args.length) {
			throw new IllegalArgumentException("Arity mismatch when defining fold over " + f + " (it needs "
					+ f.getArity() + " arguments, but got the arguments " + Arrays.toString(args) + ").");
		}
	}
	
	public static Fold mk(FunctionSymbol f, Term[] args, FunctionCallFactory funCalls) {
		return new Fold(f, args, funCalls);
	}
	
	public Term[] getArgs() {
		return args;
	}
	
	public FunctionSymbol getFunction() {
		return f;
	}
	
	public FunctionCall getShamCall() {
		return funCalls.make(f, args);
	}

	@Override
	public boolean isGround() {
		if (isGround != null) {
			return isGround;
		}
		for (Term arg : args) {
			if (!arg.isGround()) {
				return (isGround = false);
			}
		}
		return (isGround = true);
	}

	@Override
	public Term applySubstitution(Substitution s) {
		Term[] newArgs = new Term[args.length];
		int i = 0;
		for (Term arg : args) {
			newArgs[i] = arg.applySubstitution(s);
			i++;
		}
		return new Fold(f, newArgs, funCalls);
	}
	
	@Override
	public Term normalize(Substitution s) throws EvaluationException {
		Term[] newArgs = new Term[args.length];
		for (int i = 0; i < args.length; ++i) {
			newArgs[i] = args[i].normalize(s);
		}
		Term acc = newArgs[0];
		Constructor list = (Constructor) newArgs[1];
		FunctionDef def = funCalls.getDefManager().lookup(f);
		while (list.getSymbol().equals(BuiltInConstructorSymbol.CONS)) {
			Term[] consCell = list.getArgs();
			Term head = consCell[0];
			list = (Constructor) consCell[1];
			newArgs[0] = acc;
			newArgs[1] = head;
			acc = def.evaluate(newArgs);
		}
		return acc;
	}

	@Override
	public void varSet(Set<Var> acc) {
		for (Term arg : args) {
			arg.varSet(acc);
		}
	}

	@Override
	public void updateVarCounts(Map<Var, Integer> counts) {
		for (Term arg : args) {
			arg.updateVarCounts(counts);
		}
	}

	@Override
	public int getId() {
		throw new UnsupportedOperationException();
	}

	@Override
	public <I, O> O accept(ExprVisitor<I, O> visitor, I in) {
		return visitor.visit(this, in);
	}

	@Override
	public <I, O, E extends Throwable> O accept(ExprVisitorExn<I, O, E> visitor, I in) throws E {
		return visitor.visit(this, in);
	}
	
	@Override
	public String toString() {
		String s = "fold[" + f + "](";
		for (int i = 0; i < args.length; ++i) {
			s += args[i];
			if (i < args.length -1) {
				s += ", ";
			}
		}
		return s + ")";
	}

}
