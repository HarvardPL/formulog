package formulog.parsing;

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

import static formulog.util.Util.map;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import formulog.ast.Var;
import formulog.symbols.FunctionSymbol;
import formulog.symbols.parameterized.Param;
import formulog.types.FunctorType;
import formulog.types.Types.Type;
import formulog.util.Pair;
import formulog.util.Util;
import formulog.parsing.generated.FormulogBaseVisitor;
import formulog.parsing.generated.FormulogParser.FunDefLHSContext;
import formulog.parsing.generated.FormulogParser.IntParamContext;
import formulog.parsing.generated.FormulogParser.ParameterContext;
import formulog.parsing.generated.FormulogParser.ParameterListContext;
import formulog.parsing.generated.FormulogParser.TypeParamContext;
import formulog.parsing.generated.FormulogParser.WildCardParamContext;

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
		if (isNested) {
			AtomicInteger cnt = Util.lookupOrCreate(pc.nestedFunctionCounters(), name, () -> new AtomicInteger());
			name += "$" + cnt.getAndIncrement();
		}
		TypeExtractor typeExtractor = new TypeExtractor(pc);
		List<Type> argTypes = typeExtractor.extract(ctx.args.type());
		Type retType = typeExtractor.extract(ctx.retType);
		FunctionSymbol sym = pc.symbolManager().createFunctionSymbol(name, argTypes.size(),
				new FunctorType(argTypes, retType));
		List<Var> args = map(ctx.args.VAR(), x -> Var.make(x.getText()));
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

}
