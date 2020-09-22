package edu.harvard.seas.pl.formulog.parsing;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogBaseVisitor;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FunDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.IntParamContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ParameterContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ParameterListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeParamContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.WildCardParamContext;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

final class ParsingUtil {

	private ParsingUtil() {
		throw new AssertionError();
	}

	public static List<Param> extractParams(ParsingContext pc, ParameterListContext ctx) {
		List<Param> l = new ArrayList<>();
		for (ParameterContext param : ctx.parameter()) {
			l.add(extractParam(pc, param));
		}
		return l;
	}

	public static Param extractParam(ParsingContext pc, ParameterContext ctx) {
		return ctx.accept(new FormulogBaseVisitor<Param>() {

			@Override
			public Param visitWildCardParam(WildCardParamContext ctx) {
				return Param.wildCard();
			}
			
			@Override
			public Param visitTypeParam(TypeParamContext ctx) {
				TypeExtractor typeExtractor = new TypeExtractor(pc);
				return Param.wildCard(typeExtractor.extract(ctx.type()));
			}
			
			@Override
			public Param visitIntParam(IntParamContext ctx) {
				return Param.nat(Integer.parseInt(ctx.INT().getText()));
			}

		});
	}

	public static Pair<FunctionSymbol, List<Var>> extractFunDeclaration(ParsingContext pc, FunDefLHSContext ctx,
			boolean isNested) {
		String name = ctx.ID().getText();
		if (pc.symbolManager().hasConstructorSymbolWithName(name)) {
			throw new RuntimeException("Cannot create a function with name of constructor: " + name);
		}
		if (isNested) {
			AtomicInteger cnt = Util.lookupOrCreate(pc.nestedFunctionCounters(), name, () -> new AtomicInteger());
			name += "$" + cnt.getAndIncrement();
		}
		TypeExtractor typeExtractor = new TypeExtractor(pc);
		List<Type> argTypes = typeExtractor.extract(ctx.args.type());
		Type retType = typeExtractor.extract(ctx.retType);
		FunctionSymbol sym = pc.symbolManager().createFunctionSymbol(name, argTypes.size(),
				new FunctorType(argTypes, retType));
		List<Var> args = map(ctx.args.var(), x -> Var.fresh(x.getText()));
		if (args.size() != new HashSet<>(args).size()) {
			throw new RuntimeException(
					"Cannot use the same variable multiple times in a function declaration: " + name);
		}
		return new Pair<>(sym, args);
	}

	public static List<Pair<FunctionSymbol, List<Var>>> extractFunDeclarations(ParsingContext pc,
			List<FunDefLHSContext> ctxs, boolean isNested) {
		return map(ctxs, ctx -> extractFunDeclaration(pc, ctx, isNested));
	}
	
	public static Map<String, Identifier> varsToIds(Iterable<Var> vars) {
		Map<String, Identifier> m = new HashMap<>();
		for (Var x : vars) {
			m.put(x.getName(), Identifier.make(x));
		}
		return m;
	}

}
