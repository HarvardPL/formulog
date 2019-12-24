package edu.harvard.seas.pl.formulog.symbols.parameterized;

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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.util.TodoException;

public class ParameterizedConstructorSymbol extends AbstractParameterizedSymbol<BuiltInConstructorSymbolBase> implements ConstructorSymbol {

	private ParameterizedConstructorSymbol(BuiltInConstructorSymbolBase base, List<Param> args) {
		super(base, args);
	}

	public static ParameterizedConstructorSymbol mk(BuiltInConstructorSymbolBase base, List<Param> args) {
		switch (base) {
		case ARRAY_DEFAULT:
		case ARRAY_SELECT:
		case BV_ADD:
		case BV_AND:
		case BV_BIG_CONST:
		case BV_CONST:
		case BV_MUL:
		case BV_NEG:
		case BV_OR:
		case BV_SDIV:
		case BV_SGE:
		case BV_SGT:
		case BV_SLE:
		case BV_SLT:
		case BV_SREM:
		case BV_SUB:
		case BV_TO_BV_SIGNED:
		case BV_TO_BV_UNSIGNED:
		case BV_UDIV:
		case BV_UGE:
		case BV_UGT:
		case BV_ULE:
		case BV_ULT:
		case BV_UREM:
		case BV_XOR:
		case SMT_EQ:
		case SMT_EXISTS:
		case SMT_EXISTS_PAT:
		case SMT_FORALL:
		case SMT_FORALL_PAT:
		case SMT_LET:
			break;
		case FP_ADD:
		case FP_BIG_CONST:
		case FP_CONST:
		case FP_DIV:
		case FP_EQ:
		case FP_GE:
		case FP_GT:
		case FP_IS_NAN:
		case FP_LE:
		case FP_LT:
		case FP_MUL:
		case FP_NEG:
		case FP_REM:
		case FP_SUB:
			if (args.size() == 1) {
				args = new ArrayList<>(expandAsFpAlias(args.get(0)));
			}
			break;
		case FP_TO_BV:
			if (args.size() == 2) {
				Param bv = args.get(1);
				args = new ArrayList<>(expandAsFpAlias(args.get(0)));
				args.add(bv);
			}
			break;
		case FP_TO_FP:
			if (args.size() == 2) {
				args = new ArrayList<>(expandAsFpAlias(args.get(0)));
				args.addAll(expandAsFpAlias(args.get(1)));
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
		}
		return new ParameterizedConstructorSymbol(base, args);
	}
	
	private static List<Param> expandAsFpAlias(Param param) {
		if (!param.getKind().equals(ParamKind.NAT) || !param.isGround()) {
			return Collections.singletonList(param);
		}
		TypeIndex nat = (TypeIndex) param.getType();
		switch (nat.getIndex()) {
		case 16:
			return Arrays.asList(Param.nat(5), Param.nat(11));
		case 32:
			return Arrays.asList(Param.nat(8), Param.nat(24));
		case 64:
			return Arrays.asList(Param.nat(11), Param.nat(53));
		case 128:
			return Arrays.asList(Param.nat(15), Param.nat(113));
		default:
			throw new IllegalArgumentException("Illegal floating point width alias: " + nat);
		}
	}
	
	@Override
	public ParameterizedConstructorSymbol copyWithNewArgs(List<Param> args) {
		return mk(getBase(), args);
	}

	public ConstructorSymbolType getConstructorSymbolType() {
		return ConstructorSymbolType.SOLVER_EXPR;
	}

	@Override
	public FunctorType getCompileTimeType() {
		List<Param> params = getArgs();
		throw new TodoException();
//		switch (getBase()) {
//		case ARRAY_DEFAULT:
//			break;
//		case ARRAY_SELECT:
//			break;
//		case BV_ADD:
//			break;
//		case BV_AND:
//			break;
//		case BV_BIG_CONST:
//			break;
//		case BV_CONST:
//			break;
//		case BV_MUL:
//			break;
//		case BV_NEG:
//			break;
//		case BV_OR:
//			break;
//		case BV_SDIV:
//			break;
//		case BV_SGE:
//			break;
//		case BV_SGT:
//			break;
//		case BV_SLE:
//			break;
//		case BV_SLT:
//			break;
//		case BV_SREM:
//			break;
//		case BV_SUB:
//			break;
//		case BV_TO_BV_SIGNED:
//			break;
//		case BV_TO_BV_UNSIGNED:
//			break;
//		case BV_TO_FP:
//			break;
//		case BV_UDIV:
//			break;
//		case BV_UGE:
//			break;
//		case BV_UGT:
//			break;
//		case BV_ULE:
//			break;
//		case BV_ULT:
//			break;
//		case BV_UREM:
//			break;
//		case BV_XOR:
//			break;
//		case FP_ADD:
//			break;
//		case FP_BIG_CONST:
//			break;
//		case FP_CONST:
//			break;
//		case FP_DIV:
//			break;
//		case FP_EQ:
//			break;
//		case FP_GE:
//			break;
//		case FP_GT:
//			break;
//		case FP_IS_NAN:
//			break;
//		case FP_LE:
//			break;
//		case FP_LT:
//			break;
//		case FP_MUL:
//			break;
//		case FP_NEG:
//			break;
//		case FP_REM:
//			break;
//		case FP_SUB:
//			break;
//		case FP_TO_BV:
//			break;
//		case FP_TO_FP:
//			break;
//		case SMT_EQ:
//			break;
//		case SMT_EXISTS:
//			break;
//		case SMT_EXISTS_PAT:
//			break;
//		case SMT_FORALL:
//			break;
//		case SMT_FORALL_PAT:
//			break;
//		case SMT_LET:
//			break;
//		default:
//			break;
//		}
	}
	
	private static FunctorType mkType(Type... types) {
		return new FunctorType(types);
	}

}
