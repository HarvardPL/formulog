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

import static edu.harvard.seas.pl.formulog.util.Util.map;

import java.util.ArrayList;
import java.util.List;

import edu.harvard.seas.pl.formulog.parsing.generated.FormulogBaseVisitor;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ParenTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TupleTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeRefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeVarContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogVisitor;
import edu.harvard.seas.pl.formulog.symbols.IndexedTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.BuiltInTypesFactory;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.util.Pair;

class TypeExtractor {

	private final ParsingContext pc;

	public TypeExtractor(ParsingContext parsingContext) {
		pc = parsingContext;
	}

	public Type extract(TypeContext ctx) {
		return ctx.accept(typeExtractor);
	}

	public List<Type> extract(List<TypeContext> ctxs) {
		List<Type> l = new ArrayList<>();
		for (TypeContext ctx : ctxs) {
			l.add(extract(ctx));
		}
		return l;
	}

	private final FormulogVisitor<Type> typeExtractor = new FormulogBaseVisitor<Type>() {

		@Override
		public Type visitTupleType(TupleTypeContext ctx) {
			List<Type> typeArgs = map(ctx.type0(), t -> t.accept(this));
			if (typeArgs.size() == 1) {
				return typeArgs.get(0);
			}
			TypeSymbol sym = pc.symbolManager().lookupTupleTypeSymbol(typeArgs.size());
			return AlgebraicDataType.make(sym, typeArgs);
		}

		@Override
		public Type visitTypeVar(TypeVarContext ctx) {
			return TypeVar.get(ctx.getText());
		}

		@Override
		public Type visitTypeRef(TypeRefContext ctx) {
			List<Type> params;
			if (ctx.type0() != null) {
				params = new ArrayList<>();
				params.add(ctx.type0().accept(this));
			} else {
				params = map(ctx.type(), t -> t.accept(this));
			}
			String s = ctx.ID().getText();
			List<Integer> indices = ParsingUtil.extractIndices(ctx.index());
			switch (s) {
			case "i32":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type i32 does not have any type parameters.");
				}
				return BuiltInTypesFactory.i32;
			case "i64":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type i64 does not have any type parameters.");
				}
				return BuiltInTypesFactory.i64;
			case "fp32":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type fp32 does not have any type parameters.");
				}
				return BuiltInTypesFactory.fp32;
			case "fp64":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type fp64 does not have any type parameters.");
				}
				return BuiltInTypesFactory.fp64;
			case "string":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type string does not have any type parameters.");
				}
				return BuiltInTypesFactory.string;
			default:
				String name = ctx.ID().getText();
				TypeSymbol sym;
				if (!indices.isEmpty()) {
					Pair<IndexedTypeSymbol, List<Integer>> p = pc.symbolManager().lookupIndexedTypeSymbol(name,
							indices);
					sym = p.fst();
					indices = p.snd();
					params.addAll(map(indices, i -> TypeIndex.make(i)));
				} else {
					Symbol sym2 = pc.symbolManager().lookupSymbol(name);
					if (!(sym2 instanceof TypeSymbol)) {
						throw new RuntimeException("Not a type symbol: " + sym2);
					}
					sym = (TypeSymbol) sym2;
				}
				// XXX Update this to make sure you don't create types with nested smts or syms
				return pc.typeManager().lookup(sym, params);
			}
		}

		@Override
		public Type visitParenType(ParenTypeContext ctx) {
			return ctx.type().accept(this);
		}

	};

}
