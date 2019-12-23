//package edu.harvard.seas.pl.formulog.ast;
//
///*-
// * #%L
// * FormuLog
// * %%
// * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
// * %%
// * Licensed under the Apache License, Version 2.0 (the "License");
// * you may not use this file except in compliance with the License.
// * You may obtain a copy of the License at
// * 
// *      http://www.apache.org/licenses/LICENSE-2.0
// * 
// * Unless required by applicable law or agreed to in writing, software
// * distributed under the License is distributed on an "AS IS" BASIS,
// * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// * See the License for the specific language governing permissions and
// * limitations under the License.
// * #L%
// */
//
//import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
//import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
//import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
//
//public class PreConstructor extends PreFunctor<ParameterizedConstructorSymbol> {
//
//	private PreConstructor(ParameterizedConstructorSymbol sym, Term[] args) {
//		super(sym, args);
//	}
//	
//	public static PreConstructor make(ParameterizedConstructorSymbol sym, Term[] args) {
//		return new PreConstructor(sym, args);
//	}
//
//	@Override
//	public Term copyWithNewArgs(Term[] args) {
//		return make(getSymbol(), args);
//	}
//
//	@Override
//	public <I, O> O accept(TermVisitor<I, O> v, I in) {
//		return v.visit(this, in);
//	}
//
//	@Override
//	public <I, O, E extends Throwable> O accept(TermVisitorExn<I, O, E> v, I in) throws E {
//		return v.visit(this, in);
//	}
//
//	@Override
//	public boolean containsUnevaluatedTerm() {
//		for (Term arg : getArgs()) {
//			if (arg.containsUnevaluatedTerm()) {
//				return true;
//			}
//		}
//		return false;
//	}
//
//}
