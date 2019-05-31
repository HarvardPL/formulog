package edu.harvard.seas.pl.formulog.smt;

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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Function;

import org.jgrapht.Graph;
import org.jgrapht.alg.KosarajuStrongConnectivityInspector;
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.traverse.TopologicalOrderIterator;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverUninterpretedFunction;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.Expr;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibParser.SmtLibParseException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.IndexedSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeChecker;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.util.DedupWorkList;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class SmtLibShim {

	public static enum Status {
		SATISFIABLE, UNSATISFIABLE, UNKNOWN
	}

	private final BufferedReader in;
	private final PrintWriter out;
	private final Set<Symbol> declaredSorts = new HashSet<>();
	private final Map<SolverVariable, String> declaredSymbols = new HashMap<>();
	private final Map<String, SolverVariable> symbolLookup = new HashMap<>();
	private final Set<Symbol> declaredUninterpFuns = new HashSet<>();
	private final SymbolManager symbolManager;
	private volatile Iterator<Type> typeAnnotations;
	private int cnt;

	public SmtLibShim(Reader in, Writer out, SymbolManager symbolManager) {
		this.in = new BufferedReader(in);
		this.out = new PrintWriter(out);
		this.symbolManager = symbolManager;
	}

	public void makeAssertion(SmtLibTerm assertion) {
		declareSorts(assertion);
		declareSymbolsAndFuns(assertion);
		typeAnnotations = (new MiniTypeInferer()).inferTypes(assertion).iterator();
		print("(assert ");
		assertion.toSmtLib(this);
		print(")");
		assert !typeAnnotations.hasNext();
		out.flush();
	}

	public void reset() {
		declaredSorts.clear();
		declaredSymbols.clear();
		symbolLookup.clear();
		declaredUninterpFuns.clear();
		println("(reset)");
		out.flush();
	}

	public Status checkSat(Integer timeout) throws EvaluationException {
		if (timeout != null && timeout >= 0) {
			println("(set-option :timeout " + timeout + ")");

		}
		println("(check-sat)");
		out.flush();
		String result;
		try {
			result = in.readLine();
			if (result.equals("sat")) {
				return Status.SATISFIABLE;
			} else if (result.equals("unsat")) {
				return Status.UNSATISFIABLE;
			} else if (result.equals("unknown")) {
				return Status.UNKNOWN;
			} else {
				throw new EvaluationException("Problem with evaluating Z3!");
			}
		} catch (IOException e) {
			throw new EvaluationException("Problem with evaluating Z3: " + e.getMessage());
		}
	}

	public Map<SolverVariable, Term> getModel() throws EvaluationException {
		println("(get-model)");
		out.flush();
		try {
			return parseModel();
		} catch (IOException e) {
			throw new EvaluationException("Problem with evaluating Z3: " + e.getMessage());
		} catch (SmtLibParseException e) {
			throw new EvaluationException("Problem parsing Z3 output: " + e.getMessage());
		}
	}

	public Map<SolverVariable, Term> parseModel() throws EvaluationException, IOException, SmtLibParseException {
		SmtLibParser p = new SmtLibParser(symbolManager, symbolLookup);
		return p.getModel(in);
	}

	public void print(String s) {
		out.print(s);
	}

	public void println(String s) {
		out.println(s);
	}

	public void print(SolverVariable x) {
		String s = declaredSymbols.get(x);
		if (s == null) {
			throw new NoSuchElementException(x.toString());
		}
		print(s);
	}

	public void print(Symbol sym) {
		print(stringifySymbol(sym));
	}

	public void print(Type type) {
		print(stringifyType(type));
	}

	public String getTypeAnnotation(Constructor c) {
		Symbol sym = c.getSymbol();
		FunctorType ft = (FunctorType) sym.getCompileTimeType();
		if (needsTypeAnnotation(sym, ft.getArgTypes(), ft.getRetType())) {
			return stringifyType(typeAnnotations.next());
		}
		return null;
	}

	private String freshSymbol() {
		return "x" + cnt++;
	}

	private void declareSymbolsAndFuns(SmtLibTerm t) {
		t.visit(new TermVisitor<Void, Void>() {

			@Override
			public Void visit(Var t, Void in) {
				throw new AssertionError("impossible");
			}

			@Override
			public Void visit(Constructor c, Void in) {
				if (c instanceof SolverVariable) {
					SolverVariable var = (SolverVariable) c;
					if (!declaredSymbols.containsKey(var)) {
						String s = freshSymbol();
						declaredSymbols.put(var, s);
						symbolLookup.put(s, var);
						print("(declare-const " + s + " ");
						FunctorType ft = (FunctorType) var.getSymbol().getCompileTimeType();
						print(stringifyType(ft.getRetType()));
						println(")");
					}
					return null;
				}
				for (Term arg : c.getArgs()) {
					arg.visit(this, in);
				}
				if (c instanceof SolverUninterpretedFunction) {
					Symbol sym = c.getSymbol();
					if (declaredUninterpFuns.add(sym)) {
						print("(declare-fun " + stringifySymbol(sym) + " (");
						FunctorType ft = (FunctorType) sym.getCompileTimeType();
						for (Iterator<Type> it = ft.getArgTypes().iterator(); it.hasNext();) {
							print(stringifyType(it.next()));
							if (it.hasNext()) {
								print(" ");
							}
						}
						println(") " + stringifyType(ft.getRetType()) + ")");
					}
				}
				return null;
			}

			@Override
			public Void visit(Primitive<?> p, Void in) {
				return null;
			}

			@Override
			public Void visit(Expr expr, Void in) {
				throw new AssertionError("impossible");
			}

		}, null);
	}

	private void declareSorts(SmtLibTerm t) {
		SortDependencyFinder depends = new SortDependencyFinder(t);
		StrongConnectivityAlgorithm<Symbol, DefaultEdge> k = new KosarajuStrongConnectivityInspector<>(
				depends.compute());
		TopologicalOrderIterator<Graph<Symbol, DefaultEdge>, DefaultEdge> topo = new TopologicalOrderIterator<>(
				k.getCondensation());
		while (topo.hasNext()) {
			Graph<Symbol, DefaultEdge> scc = topo.next();
			declareSorts(scc.vertexSet());
		}
	}

	private void declareSorts(Set<Symbol> sorts) {
		assert !sorts.isEmpty();
		Symbol sym = sorts.iterator().next();
		if (sym.getSymbolType().equals(SymbolType.SOLVER_UNINTERPRETED_SORT)) {
			assert sorts.size() == 1;
			declareUninterpretedSort(sym);
		} else {
			assert sym.getSymbolType().equals(SymbolType.TYPE);
			declareAdtSorts(sorts);
		}
	}

	private void declareUninterpretedSort(Symbol sort) {
		assert sort.getSymbolType().equals(SymbolType.SOLVER_UNINTERPRETED_SORT);
		println("(declare-sort " + stringifySymbol(sort) + " " + sort.getArity() + ")");
	}
	
	private void declareAdtSorts(Set<Symbol> sorts) {
		assert !sorts.isEmpty();
		print("(declare-datatypes ( ");
		for (Symbol sym : sorts) {
			assert sym.getSymbolType().equals(SymbolType.TYPE);
			print("(" + stringifySymbol(sym) + " " + sym.getArity() + ") ");
		}
		print(") (");
		for (Symbol sym : sorts) {
			declareAdtSort(AlgebraicDataType.make(sym));
		}
		println("))");
	}

	private void declareAdtSort(AlgebraicDataType type) {
		print("\n  (par (");
		for (Iterator<Type> it = type.getTypeArgs().iterator(); it.hasNext();) {
			print(stringifyType(it.next()));
			if (it.hasNext()) {
				print(" ");
			}
		}
		print(") (");
		for (ConstructorScheme c : type.getConstructors()) {
			declareConstructor(c);
		}
		print("))");
	}

	private void declareConstructor(ConstructorScheme c) {
		print("\n    (");
		print(stringifySymbol(c.getSymbol()));
		Iterator<Symbol> getterSyms = c.getGetterSymbols().iterator();
		for (Type t : c.getTypeArgs()) {
			String getter = stringifySymbol(getterSyms.next());
			print(" (" + getter + " " + stringifyType(t) + ")");
		}
		print(")");
	}

	private String stringifySymbol(Symbol sym) {
		return "|" + sym + "|";
	}

	private String stringifyType(Type type) {
		return type.visit(new TypeVisitor<Void, String>() {

			@Override
			public String visit(TypeVar typeVar, Void in) {
				return "|" + typeVar + "|";
			}

			@Override
			public String visit(AlgebraicDataType algebraicType, Void in) {
				Symbol sym = algebraicType.getSymbol();
				if (sym instanceof IndexedSymbol) {
					return stringifyIndexedSymbol((IndexedSymbol) sym, algebraicType.getTypeArgs());
				}
				if (sym instanceof BuiltInTypeSymbol) {
					switch ((BuiltInTypeSymbol) sym) {
					case BOOL_TYPE:
						return "Bool";
					case STRING_TYPE:
						return "String";
					case ARRAY_TYPE: {
						String s = "(Array ";
						for (Type t : algebraicType.getTypeArgs()) {
							s += " " + stringifyType(t);
						}
						return s + ")";
					}
					case INT_TYPE:
						return "Int";
					case SMT_TYPE:
					case SYM_TYPE:
						return stringifyType(algebraicType.getTypeArgs().get(0));
					default:
						break;
					}
				}
				if (sym.getArity() == 0) {
					return stringifySymbol(sym);
				}
				String s = "(" + stringifySymbol(sym);
				for (Type t : algebraicType.getTypeArgs()) {
					s += " " + stringifyType(t);
				}
				return s + ")";
			}

			@Override
			public String visit(OpaqueType opaqueType, Void in) {
				throw new AssertionError("impossible");
			}

			private String stringifyIndexedSymbol(IndexedSymbol sym, List<Type> typeArgs) {
				Function<Type, Integer> forceIdx = t -> ((TypeIndex) t).getIndex();
				switch (sym) {
				case BV:
					return "(_ BitVec " + forceIdx.apply(typeArgs.get(0)) + ")";
				case FP:
					int idx1 = forceIdx.apply(typeArgs.get(0));
					int idx2 = forceIdx.apply(typeArgs.get(1));
					return "(_ FloatingPoint " + idx1 + " " + idx2 + ")";
				default:
					throw new AssertionError();
				}
			}

			@Override
			public String visit(TypeIndex typeIndex, Void in) {
				throw new AssertionError("shouldn't happen");
			}

		}, null);
	}

	private class SortDependencyFinder {

		private final SmtLibTerm t;

		public SortDependencyFinder(SmtLibTerm t) {
			this.t = t;
		}

		public Graph<Symbol, DefaultEdge> compute() {
			DedupWorkList<Symbol> w = extractTypesFromTerm();
			return createGraph(w);
		}

		private DedupWorkList<Symbol> extractTypesFromTerm() {
			DedupWorkList<Symbol> w = new DedupWorkList<>();
			t.visit(new TermVisitor<Void, Void>() {

				@Override
				public Void visit(Var t, Void in) {
					throw new AssertionError("impossible");
				}

				@Override
				public Void visit(Constructor c, Void in) {
					FunctorType ft = (FunctorType) c.getSymbol().getCompileTimeType();
					Type type = ft.getRetType();
					for (Symbol sym : extractTypeSymbols(type)) {
						push(sym, w);
					}
					if (!(c instanceof SolverVariable)) {
						for (Term tt : c.getArgs()) {
							tt.visit(this, in);
						}
					}
					return null;
				}

				@Override
				public Void visit(Primitive<?> p, Void in) {
					return null;
				}

				@Override
				public Void visit(Expr expr, Void in) {
					throw new AssertionError("impossible");
				}

			}, null);
			return w;
		}

		private void push(Symbol sym, DedupWorkList<Symbol> w) {
			if (isDeclarableTypeSymbol(sym)) {
				w.push(sym);
			}
		}

		private Graph<Symbol, DefaultEdge> createGraph(DedupWorkList<Symbol> w) {
			Graph<Symbol, DefaultEdge> g = new DefaultDirectedGraph<>(DefaultEdge.class);
			while (!w.isEmpty()) {
				Symbol sym = w.pop();
				assert isDeclarableTypeSymbol(sym);
				g.addVertex(sym);
				AlgebraicDataType type = AlgebraicDataType.make(sym);
				if (sym.getSymbolType().equals(SymbolType.SOLVER_UNINTERPRETED_SORT)) {
					continue;
				}
				for (ConstructorScheme c : type.getConstructors()) {
					for (Type typeArg : c.getTypeArgs()) {
						for (Symbol other : extractTypeSymbols(typeArg)) {
							push(other, w);
							if (isDeclarableTypeSymbol(other)) {
								g.addVertex(other);
								g.addEdge(other, sym);
							}
						}
					}
				}
			}
			return g;
		}

		private Set<Symbol> extractTypeSymbols(Type type) {
			Set<Symbol> syms = new HashSet<>();
			type.visit(new TypeVisitor<Void, Void>() {

				@Override
				public Void visit(TypeVar typeVar, Void in) {
					return null;
				}

				@Override
				public Void visit(AlgebraicDataType algebraicType, Void in) {
					syms.add(algebraicType.getSymbol());
					for (Type typeArg : algebraicType.getTypeArgs()) {
						typeArg.visit(this, in);
					}
					return null;
				}

				@Override
				public Void visit(OpaqueType opaqueType, Void in) {
					throw new AssertionError("impossible");
				}

				@Override
				public Void visit(TypeIndex typeIndex, Void in) {
					return null;
				}

			}, null);
			return syms;
		}

		private boolean isDeclarableTypeSymbol(Symbol sym) {
			assert sym.getSymbolType().isTypeSymbol();
			if (sym instanceof IndexedSymbol) {
				switch ((IndexedSymbol) sym) {
				case BV:
				case FP:
					return false;
				default:
					throw new AssertionError();
				}
			}
			if (sym instanceof BuiltInTypeSymbol) {
				switch ((BuiltInTypeSymbol) sym) {
				case SMT_TYPE:
				case SYM_TYPE:
				case BOOL_TYPE:
				case STRING_TYPE:
				case ARRAY_TYPE:
				case FORMULA_VAR_LIST_TYPE:
				case HETEROGENEOUS_LIST_TYPE:
				case INT_TYPE:
					return false;
				case CMP_TYPE:
				case LIST_TYPE:
				case OPTION_TYPE:
					return true;
				case MODEL_TYPE:
					throw new AssertionError("models shouldn't appear in formulae");
				default:
					throw new AssertionError("impossible");
				}
			}
			return true;
		}

	}

	private class MiniTypeInferer {

		private final Deque<Pair<Type, Type>> constraints = new ArrayDeque<>();
		private final Map<TypeVar, Type> subst = new HashMap<>();

		public List<Type> inferTypes(Term t) {
			constraints.clear();
			subst.clear();
			List<Type> types = inferTypes1(t);
			unifyConstraints();
			for (TypeVar x : Types.getTypeVars(types)) {
				if (TypeChecker.lookupType(x, subst).isVar()) {
					subst.put(x, BuiltInTypes.bool);
				}
			}
			return Util.map(types, ty -> TypeChecker.simplify(ty.applySubst(subst)));
		}

		private List<Type> inferTypes1(Term t) {
			List<Type> types = new ArrayList<>();
			t.visit(new TermVisitor<Void, Type>() {

				@Override
				public Type visit(Var t, Void in) {
					throw new AssertionError("impossible");
				}

				@Override
				public Type visit(Constructor c, Void in) {
					Symbol sym = c.getSymbol();
					FunctorType ft = (FunctorType) sym.getCompileTimeType().freshen();
					Type ty = ft.getRetType();
					List<Type> args = ft.getArgTypes();
					if (needsTypeAnnotation(sym, args, ty)) {
						types.add(ty);
					}
					if (!(c instanceof SolverVariable)) {
						Iterator<Type> it = args.iterator();
						for (Term tt : c.getArgs()) {
							constraints.add(new Pair<>(tt.visit(this, in), it.next()));
						}
					}
					return ty;
				}

				@Override
				public Type visit(Primitive<?> p, Void in) {
					return p.getType();
				}

				@Override
				public Type visit(Expr expr, Void in) {
					throw new AssertionError("impossible");
				}

			}, null);
			return types;
		}

		private void unifyConstraints() {
			TypeVisitor<Type, Void> unifier = new TypeVisitor<Type, Void>() {

				@Override
				public Void visit(TypeVar typeVar, Type other) {
					throw new AssertionError("impossible");
				}

				@Override
				public Void visit(AlgebraicDataType algebraicType, Type other) {
					AlgebraicDataType otherAdt = (AlgebraicDataType) other;
					Iterator<Type> it = otherAdt.getTypeArgs().iterator();
					for (Type arg : algebraicType.getTypeArgs()) {
						constraints.add(new Pair<>(arg, it.next()));
					}
					return null;
				}

				@Override
				public Void visit(OpaqueType opaqueType, Type other) {
					throw new AssertionError("impossible");
				}

				@Override
				public Void visit(TypeIndex typeIndex, Type other) {
					assert typeIndex.equals(other);
					return null;
				}

			};
			while (!constraints.isEmpty()) {
				Pair<Type, Type> p = constraints.pop();
				Type t1 = TypeChecker.simplify(TypeChecker.lookupType(p.fst(), subst));
				Type t2 = TypeChecker.simplify(TypeChecker.lookupType(p.snd(), subst));
				if (t1.isVar()) {
					handleVar((TypeVar) t1, t2);
				} else if (t2.isVar()) {
					handleVar((TypeVar) t2, t1);
				} else {
					t1.visit(unifier, t2);
				}

			}
		}

		private void handleVar(TypeVar x, Type t) {
			if (t.isVar()) {
				TypeVar y = (TypeVar) t;
				if (x.compareTo(y) < 0) {
					subst.put(x, y);
				} else if (x.compareTo(y) > 0) {
					subst.put(y, x);
				}
				return;
			}
			subst.put(x, t);
		}

	}

	private static boolean needsTypeAnnotation(Symbol constructorSymbol, List<Type> argTypes, Type retType) {
		return !Types.getTypeVars(argTypes).containsAll(Types.getTypeVars(retType));
	}

}
