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
import java.util.List;

import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.util.TodoException;

public class ParameterizedConstructorSymbol extends AbstractParameterizedSymbol<BuiltInConstructorSymbolBase> implements ParameterizedFunctorSymbol {

	private ParameterizedConstructorSymbol(BuiltInConstructorSymbolBase base, List<ParamElt> args) {
		super(base, args);
	}

	public static ParameterizedConstructorSymbol mk(BuiltInConstructorSymbolBase base, List<ParamElt> args) {
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
			if (args.size() == 1 && args.get(0) instanceof NatParam) {
				args = new ArrayList<>(((NatParam) args.get(0)).expandAsFpAlias());
			}
			break;
		case FP_TO_BV:
			if (args.size() == 2 && args.get(0) instanceof NatParam) {
				ParamElt bv = args.get(1);
				args = new ArrayList<>(((NatParam) args.get(0)).expandAsFpAlias());
				args.add(bv);
			}
			break;
		case FP_TO_FP:
			if (args.size() == 2 && args.get(0) instanceof NatParam && args.get(1) instanceof NatParam) {
				args = new ArrayList<>(((NatParam) args.get(0)).expandAsFpAlias());
				args.addAll(((NatParam) args.get(1)).expandAsFpAlias());
			}
			break;
		case BV_TO_FP:
			if (args.size() == 2 && args.get(1) instanceof NatParam) {
				List<ParamElt> newArgs = new ArrayList<>();
				newArgs.add(args.get(0));
				newArgs.addAll(((NatParam) args.get(1)).expandAsFpAlias());
				args = newArgs;
			}
			break;
		}
		return new ParameterizedConstructorSymbol(base, args);
	}
	
	@Override
	public ParameterizedSymbol copyWithNewArgs(List<ParamElt> args) {
		return mk(getBase(), args);
	}

	@Override
	public PreFunctorType getPreType() {
		throw new TodoException();
	}

	@Override
	public Symbol mkFinal() {
		throw new TodoException();
	}
	
}
