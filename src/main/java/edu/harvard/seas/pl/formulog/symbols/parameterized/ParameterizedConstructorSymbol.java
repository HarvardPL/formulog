package edu.harvard.seas.pl.formulog.symbols.parameterized;

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

import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.array;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bv;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.fp64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i32;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.i64;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.int_;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smtPattern;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smtWrappedVar;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.sym;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class ParameterizedConstructorSymbol extends AbstractParameterizedSymbol<BuiltInConstructorSymbolBase>
		implements ConstructorSymbol {

	private final FunctorType type;
	private static final Map<Pair<BuiltInConstructorSymbolBase, List<Param>>, ParameterizedConstructorSymbol> memo = new ConcurrentHashMap<>();

	private ParameterizedConstructorSymbol(BuiltInConstructorSymbolBase base, List<Param> args) {
		super(base, args);
		this.type = makeType();
	}

	public static ParameterizedConstructorSymbol mk(BuiltInConstructorSymbolBase base, List<Param> args) {
		switch (base) {
		case ARRAY_DEFAULT:
		case ARRAY_SELECT:
		case BV_BIG_CONST:
		case BV_CONST:
		case BV_SGE:
		case BV_SGT:
		case BV_SLE:
		case BV_SLT:
		case BV_TO_BV_SIGNED:
		case BV_TO_BV_UNSIGNED:
		case BV_UGE:
		case BV_UGT:
		case BV_ULE:
		case BV_ULT:
		case BV_CONCAT:
		case BV_EXTRACT:
		case SMT_EQ:
		case SMT_LET:
		case SMT_PAT:
		case SMT_WRAP_VAR:
		case SMT_VAR:
		case BV_TO_INT:
		case INT_TO_BV:
			break;
		case FP_BIG_CONST:
		case FP_CONST:
		case FP_EQ:
		case FP_GE:
		case FP_GT:
		case FP_IS_NAN:
		case FP_LE:
		case FP_LT:
			if (args.size() == 1) {
				args = new ArrayList<>(expandAsFpAlias(args.get(0)));
			}
			break;
		case FP_TO_SBV:
		case FP_TO_UBV:
			if (args.size() == 2) {
				Param bv = args.get(1);
				args = new ArrayList<>(expandAsFpAlias(args.get(0)));
				args.add(bv);
			}
			break;
		case FP_TO_FP:
			if (args.size() == 2) {
				Param fp1 = args.get(0);
				Param fp2 = args.get(1);
				args = new ArrayList<>(expandAsFpAlias(fp1));
				args.addAll(expandAsFpAlias(fp2));
			}
			break;
		case BV_TO_FP:
			if (args.size() == 2) {
				List<Param> newArgs = new ArrayList<>();
				newArgs.add(args.get(0));
				newArgs.addAll(expandAsFpAlias(args.get(1)));
				args = newArgs;
			}
			break;
		default:
			throw new AssertionError("Unexpected symbol: " + base);
		}
		if (args.isEmpty()) {
			args = Param.wildCards(base.getNumParams());
		}
		List<Param> args2 = List.copyOf(args);
		return new ParameterizedConstructorSymbol(base, args2);
	}

	private static List<Param> expandAsFpAlias(Param param) {
		if (!param.getKind().equals(ParamKind.NAT) || !param.isGround()) {
			return Collections.singletonList(param);
		}
		TypeIndex nat = (TypeIndex) param.getType();
		List<TypeIndex> indices = nat.expandAsFpIndex();
		List<Param> params = new ArrayList<>();
		for (TypeIndex index : indices) {
			params.add(Param.nat(index.getIndex()));
		}
		return params;
	}

	@Override
	public ParameterizedConstructorSymbol copyWithNewArgs(List<Param> args) {
		return mk(getBase(), args);
	}

	@Override
	public ParameterizedConstructorSymbol copyWithNewArgs(Param... args) {
		return copyWithNewArgs(Arrays.asList(args));
	}

	public ConstructorSymbolType getConstructorSymbolType() {
		return ConstructorSymbolType.SOLVER_EXPR;
	}

	private FunctorType makeType() {
		List<Type> types = new ArrayList<>();
		for (Param param : getArgs()) {
			types.add(param.getType());
		}
		switch (getBase()) {
		case ARRAY_DEFAULT: {
			Type a = types.get(0);
			Type b = TypeVar.fresh();
			return mkType(smt(array(a, b)), smt(b));
		}
		case ARRAY_SELECT: {
			Type a = types.get(0);
			Type b = TypeVar.fresh();
			return mkType(smt(array(a, b)), smt(a), smt(b));
		}
		case BV_BIG_CONST: {
			Type width = types.get(0);
			return mkType(i64, smt(bv(width)));
		}
		case BV_CONST: {
			Type width = types.get(0);
			return mkType(i32, smt(bv(width)));
		}
		case BV_CONCAT: {
			Type w1 = types.get(0);
			Type w2 = types.get(1);
			Type w3 = types.get(2);
			return mkType(smt(bv(w1)), smt(bv(w2)), smt(bv(w3)));
		}
		case BV_EXTRACT: {
			Type w1 = types.get(0);
			Type w2 = types.get(1);
			return mkType(smt(bv(w1)), i32, i32, smt(bv(w2)));
		}
		case INT_TO_BV:
			return mkType(smt(int_), smt(bv(types.get(0))));
		case BV_TO_INT:
			return mkType(smt(bv(types.get(0))), smt(int_));
		case BV_SGE:
		case BV_SGT:
		case BV_SLE:
		case BV_SLT:
		case BV_UGE:
		case BV_UGT:
		case BV_ULE:
		case BV_ULT: {
			Type width = types.get(0);
			return mkType(smt(bv(width)), smt(bv(width)), smt(bool));
		}
		case BV_TO_BV_SIGNED:
		case BV_TO_BV_UNSIGNED: {
			Type fromWidth = types.get(0);
			Type toWidth = types.get(1);
			return mkType(smt(bv(fromWidth)), smt(bv(toWidth)));
		}
		case BV_TO_FP: {
			Type width = types.get(0);
			Type exponent = types.get(1);
			Type significand = types.get(2);
			return mkType(smt(bv(width)), smt(fp(exponent, significand)));
		}
		case FP_BIG_CONST: {
			Type exponent = types.get(0);
			Type significand = types.get(1);
			return mkType(fp64, smt(fp(exponent, significand)));
		}
		case FP_CONST: {
			Type exponent = types.get(0);
			Type significand = types.get(1);
			return mkType(fp32, smt(fp(exponent, significand)));
		}
		case FP_EQ:
		case FP_GE:
		case FP_GT:
		case FP_LE:
		case FP_LT: {
			Type exponent = types.get(0);
			Type significand = types.get(1);
			Type fp = fp(exponent, significand);
			return mkType(smt(fp), smt(fp), smt(bool));
		}
		case FP_IS_NAN: {
			Type exponent = types.get(0);
			Type significand = types.get(1);
			return mkType(smt(fp(exponent, significand)), smt(bool));
		}
		case FP_TO_SBV:
		case FP_TO_UBV: {
			Type exponent = types.get(0);
			Type significand = types.get(1);
			Type width = types.get(2);
			return mkType(smt(fp(exponent, significand)), smt(bv(width)));
		}
		case FP_TO_FP: {
			Type exp1 = types.get(0);
			Type sig1 = types.get(1);
			Type exp2 = types.get(2);
			Type sig2 = types.get(3);
			return mkType(smt(fp(exp1, sig1)), smt(fp(exp2, sig2)));
		}
		case SMT_EQ: {
			Type ty = types.get(0);
			return mkType(smt(ty), smt(ty), smt(bool));
		}
		case SMT_LET: {
			Type a = types.get(0);
			Type b = TypeVar.fresh();
			return mkType(sym(a), smt(a), smt(b), smt(b));
		}
		case SMT_PAT: {
			return mkType(types.get(0), smtPattern);
		}
		case SMT_WRAP_VAR: {
			return mkType(sym(types.get(0)), smtWrappedVar);
		}
		case SMT_VAR: {
			return mkType(types.get(0), sym(types.get(1)));
		}
		}
		throw new AssertionError("impossible");
	}

	@Override
	public FunctorType getCompileTimeType() {
		return type;
	}

	private static FunctorType mkType(Type... types) {
		return new FunctorType(types);
	}

	@Override
	public ParameterizedSymbol makeFinal() {
		return Util.lookupOrCreate(memo, new Pair<>(getBase(), getArgs()),
				() -> new ParameterizedConstructorSymbol(getBase(), getArgs()));
	}

}
