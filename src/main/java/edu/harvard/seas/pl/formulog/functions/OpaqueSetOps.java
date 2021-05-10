package edu.harvard.seas.pl.formulog.functions;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2021 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.ast.BoolTerm;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.OpaqueSet;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

public final class OpaqueSetOps {

	private OpaqueSetOps() {
		throw new AssertionError("impossible");
	}
	
	public static final FunctionDef empty = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_EMPTY;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			return OpaqueSet.empty();
		}
		
	};
	
	public static final FunctionDef size = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_SIZE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s = (OpaqueSet) args[0];
			return I32.make(s.size());
		}
		
	};
	
	public static final FunctionDef plus = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_PLUS;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s = (OpaqueSet) args[1];
			return s.plus(args[0]);
		}
		
	};
	
	public static final FunctionDef minus = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_MINUS;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s = (OpaqueSet) args[1];
			return s.minus(args[0]);
		}
		
	};
	
	public static final FunctionDef union = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_UNION;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s1 = (OpaqueSet) args[0];
			OpaqueSet s2 = (OpaqueSet) args[1];
			return s1.union(s2);
		}
		
	};
	
	public static final FunctionDef diff = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_DIFF;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s1 = (OpaqueSet) args[0];
			OpaqueSet s2 = (OpaqueSet) args[1];
			return s1.diff(s2);
		}
		
	};
	
	public static final FunctionDef choose = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_CHOOSE;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s = (OpaqueSet) args[0];
			Pair<Term, OpaqueSet> p = s.choose();
			if (p == null) {
				return Constructors.none();
			}
			return Constructors.some(Constructors.tuple(p.fst(), p.snd()));
		}
		
	};
	
	public static final FunctionDef member = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_MEMBER;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s = (OpaqueSet) args[1];
			return BoolTerm.mk(s.member(args[0]));
		}
		
	};
	
	public static final FunctionDef singleton = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_SINGLETON;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			return OpaqueSet.singleton(args[0]);
		}
		
	};
	
	public static final FunctionDef subset = new FunctionDef() {

		@Override
		public FunctionSymbol getSymbol() {
			return BuiltInFunctionSymbol.OPAQUE_SET_SUBSET;
		}

		@Override
		public Term evaluate(Term[] args) throws EvaluationException {
			OpaqueSet s1 = (OpaqueSet) args[0];
			OpaqueSet s2 = (OpaqueSet) args[1];
			return BoolTerm.mk(s2.containsAll(s1));
		}
		
	};

}
