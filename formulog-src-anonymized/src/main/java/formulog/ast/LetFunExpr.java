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



import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import formulog.ast.Exprs.ExprVisitor;
import formulog.ast.Exprs.ExprVisitorExn;
import formulog.eval.EvaluationException;
import formulog.unification.Substitution;

public class LetFunExpr implements Expr {
	
	private final Set<NestedFunctionDef> defs;
	private final Term letBody;
	
	private LetFunExpr(Set<NestedFunctionDef> defs, Term letBody) {
		Set<NestedFunctionDef> freshDefs = new HashSet<>();
		for (NestedFunctionDef def : defs) {
			freshDefs.add(def.freshen());
		}
		this.defs = Collections.unmodifiableSet(freshDefs);
		this.letBody = letBody;
	}
	
	public static LetFunExpr make(Set<NestedFunctionDef> defs, Term letBody) {
		return new LetFunExpr(defs, letBody);
	}
	
	public Set<NestedFunctionDef> getDefs() {
		return defs;
	}
	
	public Term getLetBody() {
		return letBody;
	}

	@Override
	public boolean isGround() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term applySubstitution(Substitution s) {
		Set<NestedFunctionDef> newDefs = new HashSet<>();
		for (NestedFunctionDef def : defs) {
			newDefs.add(def.applySubstitution(s));
		}
		return make(newDefs, letBody.applySubstitution(s));
	}

	@Override
	public Term normalize(Substitution s) throws EvaluationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void varSet(Set<Var> acc) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void updateVarCounts(Map<Var, Integer> counts) {
		throw new UnsupportedOperationException();
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
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((defs == null) ? 0 : defs.hashCode());
		result = prime * result + ((letBody == null) ? 0 : letBody.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LetFunExpr other = (LetFunExpr) obj;
		if (defs == null) {
			if (other.defs != null)
				return false;
		} else if (!defs.equals(other.defs))
			return false;
		if (letBody == null) {
			if (other.letBody != null)
				return false;
		} else if (!letBody.equals(other.letBody))
			return false;
		return true;
	}
	
	@Override
	public String toString() {
		String s = "let fun ";
		for (Iterator<NestedFunctionDef> it = defs.iterator(); it.hasNext();) {
			s += it.next();
			if (it.hasNext()) {
				s += "\nand ";
			}
		}
		return s + " in\n" + letBody;
	}

}
