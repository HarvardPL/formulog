package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * FormuLog
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.util.Pair;

public class TypeCodeGen {

	private final CodeGenContext ctx;

	public TypeCodeGen(CodeGenContext ctx) {
		this.ctx = ctx;
	}

	public Pair<CppStmt, CppExpr> gen(AlgebraicDataType type) {
		List<CppStmt> acc = new ArrayList<>();
		CppExpr e = gen(acc, type);
		return new Pair<>(CppSeq.mk(acc), e);
	}

	public CppExpr gen(List<CppStmt> acc, AlgebraicDataType type) {
		return new Worker(acc, new HashMap<>()).go(type);
	}

	private class Worker {

		private final Map<TypeVar, CppExpr> env;
		private final List<CppStmt> acc;

		public Worker(List<CppStmt> acc, Map<TypeVar, CppExpr> env) {
			this.acc = acc;
			this.env = env;
		}

		public CppExpr go(Type type) {
			return type.accept(visitor, null);
		}

		TypeVisitor<Void, CppExpr> visitor = new TypeVisitor<Void, CppExpr>() {

			@Override
			public CppExpr visit(TypeVar typeVar, Void in) {
				CppExpr e = env.get(typeVar);
				if (e == null) {
					String id = ctx.newId("ty");
					acc.add(CppDecl.mk(id, CppFuncCall.mk("new_var")));
					e = CppVar.mk(id);
					env.put(typeVar, e);
				}
				return e;
			}

			@Override
			public CppExpr visit(AlgebraicDataType algebraicType, Void in) {
				TypeSymbol sym = algebraicType.getSymbol();
				CppExpr e = null;
				if (sym instanceof BuiltInTypeSymbol) {
					e = handleBuiltInType(algebraicType);
				}
				if (e != null) {
					return e;
				}
				// XXX Need to make sure this matches SMT declarations
				return mkType("|" + sym + "|", algebraicType.getTypeArgs());
			}

			@Override
			public CppExpr visit(OpaqueType opaqueType, Void in) {
				throw new AssertionError("impossible");
			}

			@Override
			public CppExpr visit(TypeIndex typeIndex, Void in) {
				throw new AssertionError("impossible");
			}

		};

		private CppExpr handleBuiltInType(AlgebraicDataType type) {
			BuiltInTypeSymbol sym = (BuiltInTypeSymbol) type.getSymbol();
			List<Type> args = type.getTypeArgs();
			switch (sym) {
			case ARRAY_TYPE:
				return mkType("Array", args);
			case BOOL_TYPE:
				return mkType("Bool", args);
			case BV: {
				int w = ((TypeIndex) args.get(0)).getIndex();
				return mkType("(_ BitVec " + w + ")");
			}
			case STRING_TYPE:
				return mkType("String", args);
			case FP: {
				int e = ((TypeIndex) args.get(0)).getIndex();
				int s = ((TypeIndex) args.get(1)).getIndex();
				return mkType("(_ FloatingPoint " + e + " " + s + ")");
			}
			case INT_TYPE:
				return mkType("Int", args);
			case LIST_TYPE:
			case OPTION_TYPE:
			case CMP_TYPE:
				break;
			case MODEL_TYPE:
			case SMT_PATTERN_TYPE:
			case SMT_TYPE:
			case SMT_WRAPPED_VAR_TYPE:
			case SYM_TYPE:
				throw new AssertionError("impossible");
			}
			return null;
		}

		private List<CppExpr> go(List<Type> types) {
			List<CppExpr> l = new ArrayList<>();
			for (Type ty : types) {
				l.add(go(ty));
			}
			return l;
		}

		private CppExpr mkType(String name) {
			return mkType(name, Collections.emptyList());
		}
		
		private CppExpr mkType(String name, List<Type> args) {
			CppExpr cppName = CppConst.mkString(name);
			String vId = ctx.newId("v");
			acc.add(CppCtor.mkInitializer("vector<Type>", vId, go(args)));
			String tyId = ctx.newId("ty");
			acc.add(CppCtor.mkInitializer("Type", tyId, cppName, CppConst.mkFalse(), CppVar.mk(vId)));
			return CppVar.mk(tyId);
		}

	}

}
