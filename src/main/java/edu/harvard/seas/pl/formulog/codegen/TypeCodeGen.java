package edu.harvard.seas.pl.formulog.codegen;

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


import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
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

	public Pair<CppStmt, CppExpr> gen(FunctorType type) {
		List<CppStmt> acc = new ArrayList<>();
		CppExpr e = gen(acc, type);
		return new Pair<>(CppSeq.mk(acc), e);
	}

	public CppExpr gen(List<CppStmt> acc, FunctorType type) {
		return new Worker(acc, new HashMap<>()).go(type);
	}
	
	public List<CppExpr> gen(List<CppStmt> acc, List<FunctorType> types) {
		List<CppExpr> es = new ArrayList<>();
		for (FunctorType ty : types) {
			gen(acc, ty);
		}
		return es;
	}
	
	public Pair<CppStmt, List<CppExpr>> gen(List<FunctorType> types) {
		List<CppStmt> acc = new ArrayList<>();
		List<CppExpr> es = gen(acc, types);
		return new Pair<>(CppSeq.mk(acc), es);
	}

	private class Worker {

		private final Map<TypeVar, CppExpr> env;
		private final List<CppStmt> acc;

		public Worker(List<CppStmt> acc, Map<TypeVar, CppExpr> env) {
			this.acc = acc;
			this.env = env;
		}

		public CppExpr go(Type type) {
			if (type instanceof FunctorType) {
				return go1((FunctorType) type);
			}
			return type.accept(visitor, null);
		}
		
		public CppExpr go1(FunctorType type) {
			CppExpr ret = go(type.getRetType());
			return CppFuncCall.mk("make_pair", mkVec(type.getArgTypes()), ret);
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
				return mkType(Integer.toString(typeIndex.getIndex()));
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
			case BV:
				return mkType("_ BitVec", args);
			case STRING_TYPE:
				return mkType("String", args);
			case FP:
				return mkType("_ FloatingPoint", args);
			case INT_TYPE:
				return mkType("Int", args);
			case LIST_TYPE:
			case OPTION_TYPE:
			case CMP_TYPE:
			case MODEL_TYPE:
			case SMT_PATTERN_TYPE:
			case SMT_TYPE:
			case SMT_WRAPPED_VAR_TYPE:
			case SYM_TYPE:
				break;
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
			CppExpr vec = mkVec(args);
			String tyId = ctx.newId("ty");
			acc.add(CppCtor.mkInitializer("Type", tyId, cppName, CppConst.mkFalse(), vec));
			return CppVar.mk(tyId);
		}
		
		private CppExpr mkVec(List<Type> args) {
			String vId = ctx.newId("v");
			acc.add(CppCtor.mkInitializer("vector<Type>", vId, go(args)));
			return CppVar.mk(vId);
		}

	}

}
