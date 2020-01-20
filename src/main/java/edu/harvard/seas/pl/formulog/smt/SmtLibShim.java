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
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.jgrapht.Graph;
import org.jgrapht.alg.KosarajuStrongConnectivityInspector;
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.traverse.TopologicalOrderIterator;

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors.SolverVariable;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.SmtLibTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibParser.SmtLibParseException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
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

public class SmtLibShim {

	private static final boolean recordTime = Configuration.timeSmt;
	private static final boolean noModel = Configuration.noModel();

	public static enum Status {
		SATISFIABLE, UNSATISFIABLE, UNKNOWN
	}

	private final BufferedReader in;
	private PrintWriter out;
	private final Map<SolverVariable, String> declaredSymbols = new HashMap<>();
	private final Deque<Set<SolverVariable>> symbolsByStackPos = new ArrayDeque<>();
	private final Map<String, SolverVariable> symbolLookup = new HashMap<>();
	private final SymbolManager symbolManager;
	private Iterator<Pair<ConstructorSymbol, Type>> typeAnnotations;
	private int cnt;

	public SmtLibShim(Reader in, Writer out, Program<?, ?> prog) {
		this.in = in != null ? new BufferedReader(in) : null;
		this.out = new PrintWriter(out);
		this.symbolManager = prog.getSymbolManager();
		symbolsByStackPos.add(new HashSet<>());
		makeDeclarations(prog);
	}

	public void redirectOutput(Writer out) {
		this.out = new PrintWriter(out);
	}

	public void makeAssertion(SmtLibTerm assertion) {
		long start = 0;
		long end = 0;
		if (recordTime) {
			start = System.currentTimeMillis();
		}
		declareSymbols(assertion);
		if (recordTime) {
			end = System.currentTimeMillis();
			Configuration.recordSmtDeclTime(end - start);
			start = end;
		}
		typeAnnotations = new MiniTypeInferer().inferTypes(assertion).iterator();
		if (recordTime) {
			end = System.currentTimeMillis();
			Configuration.recordSmtInferTime(end - start);
			start = end;
		}
		print("(assert ");
		assertion.toSmtLib(this);
		println(")");
		if (recordTime) {
			end = System.currentTimeMillis();
			Configuration.recordSmtSerialTime(end - start);
		}
		assert !typeAnnotations.hasNext() : typeAnnotations.next();
		out.flush();
	}

	public void reset() {
		declaredSymbols.clear();
		symbolLookup.clear();
		symbolsByStackPos.clear();
		println("(reset)");
		out.flush();
	}

	public void push() {
		println("(push)");
		out.flush();
		symbolsByStackPos.addLast(new HashSet<>());
	}

	public void pop() {
		println("(pop)");
		out.flush();
		for (SolverVariable x : symbolsByStackPos.removeLast()) {
			String s = declaredSymbols.remove(x);
			symbolLookup.remove(s);
		}
	}

	public Status checkSat(int timeout) throws EvaluationException {
		return checkSatAssuming(Collections.emptyList(), Collections.emptyList(), timeout);
	}

	public Status checkSatAssuming(List<SolverVariable> onVars, List<SolverVariable> offVars, int timeout)
			throws EvaluationException {
		if (timeout >= 0) {
			println("(set-option :timeout " + timeout + ")");

		}
		print("(check-sat-assuming (");
		for (SolverVariable x : onVars) {
			print(x);
			print(" ");
		}
		for (SolverVariable x : offVars) {
			print("(not ");
			print(x);
			print(") ");
		}
		println("))");
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
				throw new EvaluationException("Problem with evaluating Z3! Unexpected result: " + result);
			}
		} catch (IOException e) {
			throw new EvaluationException("Problem with evaluating Z3: " + e.getMessage());
		}
	}

	public Map<SolverVariable, Term> getModel() throws EvaluationException {
		if (noModel) {
			return Collections.emptyMap();
		}
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

	public String getTypeAnnotation(ConstructorSymbol sym) {
		if (needsTypeAnnotation(sym)) {
			Pair<ConstructorSymbol, Type> p = typeAnnotations.next();
			assert p.fst().equals(sym);
			return stringifyType(p.snd());
		}
		return null;
	}

	private String freshSymbol() {
		return "x" + cnt++;
	}

	private void declareSymbols(SmtLibTerm t) {
		t.accept(new TermVisitor<Void, Void>() {

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
						symbolsByStackPos.getLast().add(var);
						print("(declare-const " + s + " ");
						FunctorType ft = (FunctorType) var.getSymbol().getCompileTimeType();
						print(stringifyType(ft.getRetType()));
						println(")");
					}
					return null;
				}
				for (Term arg : c.getArgs()) {
					arg.accept(this, in);
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

	private void makeDeclarations(Program<?, ?> prog) {
		declareSorts(prog.getTypeSymbols());
		declareUninterpretedFunctions(prog.getUninterpretedFunctionSymbols());
		out.flush();
	}

	private void declareUninterpretedFunctions(Set<ConstructorSymbol> funcs) {
		for (ConstructorSymbol func : funcs) {
			print("(declare-fun " + stringifySymbol(func) + " (");
			FunctorType ft = func.getCompileTimeType();
			for (Iterator<Type> it = ft.getArgTypes().iterator(); it.hasNext();) {
				print(stringifyType(it.next()));
				if (it.hasNext()) {
					print(" ");
				}
			}
			println(") " + stringifyType(ft.getRetType()) + ")");

		}
	}

	private void declareSorts(Set<TypeSymbol> sorts) {
		SortDependencyFinder depends = new SortDependencyFinder(sorts);
		StrongConnectivityAlgorithm<TypeSymbol, DefaultEdge> k = new KosarajuStrongConnectivityInspector<>(
				depends.compute());
		TopologicalOrderIterator<Graph<TypeSymbol, DefaultEdge>, DefaultEdge> topo = new TopologicalOrderIterator<>(
				k.getCondensation());
		while (topo.hasNext()) {
			Graph<TypeSymbol, DefaultEdge> scc = topo.next();
			declareScc(scc.vertexSet());
		}
	}

	private void declareScc(Set<TypeSymbol> sorts) {
		assert !sorts.isEmpty();
		TypeSymbol sym = sorts.iterator().next();
		if (sym.isUninterpretedSort()) {
			assert sorts.size() == 1;
			declareUninterpretedSort(sym);
		} else {
			assert sym.isNormalType();
			declareAdtSorts(sorts);
		}
	}

	private void declareUninterpretedSort(TypeSymbol sort) {
		assert sort.isUninterpretedSort();
		println("(declare-sort " + stringifySymbol(sort) + " " + sort.getArity() + ")");
	}

	private void declareAdtSorts(Set<TypeSymbol> sorts) {
		assert !sorts.isEmpty();
		print("(declare-datatypes ( ");
		for (TypeSymbol sym : sorts) {
			assert sym.isNormalType();
			print("(" + stringifySymbol(sym) + " " + sym.getArity() + ") ");
		}
		print(") (");
		for (TypeSymbol sym : sorts) {
			declareAdtSort(AlgebraicDataType.makeWithFreshArgs(sym));
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
		Iterator<ConstructorSymbol> getterSyms = c.getGetterSymbols().iterator();
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
		return type.accept(new TypeVisitor<Void, String>() {

			@Override
			public String visit(TypeVar typeVar, Void in) {
				return "|" + typeVar + "|";
			}

			@Override
			public String visit(AlgebraicDataType algebraicType, Void in) {
				TypeSymbol sym = algebraicType.getSymbol();
				if (sym instanceof BuiltInTypeSymbol) {
					List<Type> typeArgs = algebraicType.getTypeArgs();
					switch ((BuiltInTypeSymbol) sym) {
					case BOOL_TYPE:
						return "Bool";
					case STRING_TYPE:
						return "String";
					case ARRAY_TYPE: {
						String s = "(Array ";
						for (Type t : typeArgs) {
							s += " " + stringifyType(t);
						}
						return s + ")";
					}
					case INT_TYPE:
						return "Int";
					case SMT_TYPE:
					case SYM_TYPE:
						return stringifyType(algebraicType.getTypeArgs().get(0));
					case BV:
						return "(_ BitVec " + ((TypeIndex) typeArgs.get(0)).getIndex() + ")";
					case FP:
						int idx1 = ((TypeIndex) typeArgs.get(0)).getIndex();
						int idx2 = ((TypeIndex) typeArgs.get(1)).getIndex();
						return "(_ FloatingPoint " + idx1 + " " + idx2 + ")";
					case CMP_TYPE:
					case LIST_TYPE:
					case OPTION_TYPE:
						break;
					case MODEL_TYPE:
					case SMT_PATTERN_TYPE:
					case SMT_WRAPPED_VAR_TYPE:
					default:
						return null;
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

			@Override
			public String visit(TypeIndex typeIndex, Void in) {
				throw new AssertionError("shouldn't happen");
			}

		}, null);
	}

	private class SortDependencyFinder {

		private final DedupWorkList<TypeSymbol> w = new DedupWorkList<>();

		public SortDependencyFinder(Set<TypeSymbol> types) {
			for (TypeSymbol type : types) {
				push(type);
			}
		}

		private void push(TypeSymbol sym) {
			if (isDeclarableTypeSymbol(sym)) {
				w.push(sym);
			}
		}

		private Graph<TypeSymbol, DefaultEdge> compute() {
			Graph<TypeSymbol, DefaultEdge> g = new DefaultDirectedGraph<>(DefaultEdge.class);
			while (!w.isEmpty()) {
				TypeSymbol sym = w.pop();
				assert isDeclarableTypeSymbol(sym);
				g.addVertex(sym);
				AlgebraicDataType type = AlgebraicDataType.makeWithFreshArgs(sym);
				if (sym.isUninterpretedSort()) {
					continue;
				}
				for (ConstructorScheme c : type.getConstructors()) {
					for (Type typeArg : c.getTypeArgs()) {
						for (TypeSymbol other : extractTypeSymbols(typeArg)) {
							push(other);
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

		private Set<TypeSymbol> extractTypeSymbols(Type type) {
			Set<TypeSymbol> syms = new HashSet<>();
			type.accept(new TypeVisitor<Void, Void>() {

				@Override
				public Void visit(TypeVar typeVar, Void in) {
					return null;
				}

				@Override
				public Void visit(AlgebraicDataType algebraicType, Void in) {
					syms.add(algebraicType.getSymbol());
					for (Type typeArg : algebraicType.getTypeArgs()) {
						typeArg.accept(this, in);
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

	}

	private class MiniTypeInferer {

		private final Deque<Pair<Type, Type>> constraints = new ArrayDeque<>();
		private final Map<TypeVar, Type> subst = new HashMap<>();

		public List<Pair<ConstructorSymbol, Type>> inferTypes(Term t) {
			constraints.clear();
			subst.clear();
			List<Pair<ConstructorSymbol, Type>> types = inferTypes1(t);
			unifyConstraints();
			List<Pair<ConstructorSymbol, Type>> types2 = new ArrayList<>();
			for (Pair<ConstructorSymbol, Type> p : types) {
				types2.add(new Pair<>(p.fst(), TypeChecker.simplify(p.snd().applySubst(subst))));
			}
			return types2;
		}

		private List<Pair<ConstructorSymbol, Type>> inferTypes1(Term t) {
			List<Pair<ConstructorSymbol, Type>> types = new ArrayList<>();
			t.accept(new TermVisitor<Void, Type>() {

				@Override
				public Type visit(Var t, Void in) {
					throw new AssertionError("impossible");
				}

				@Override
				public Type visit(Constructor c, Void in) {
					ConstructorSymbol sym = c.getSymbol();
					FunctorType ft = sym.getCompileTimeType().freshen();
					Type ty = ft.getRetType();
					List<Type> args = ft.getArgTypes();
					if (needsTypeAnnotation(sym)) {
						types.add(new Pair<>(sym, ty));
					}
					if (!(c instanceof SolverVariable)) {
						Iterator<Type> it = args.iterator();
						for (Term tt : c.getArgs()) {
							constraints.add(new Pair<>(tt.accept(this, in), it.next()));
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
					t1.accept(unifier, t2);
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

	private static boolean needsTypeAnnotation(ConstructorSymbol sym) {
		if (sym instanceof ParameterizedConstructorSymbol) {
			return false;
		}
		if (sym.getConstructorSymbolType().equals(ConstructorSymbolType.VANILLA_CONSTRUCTOR)) {
			return true;
		}
		FunctorType ft = sym.getCompileTimeType();
		List<Type> args = ft.getArgTypes();
		Type ret = sym.getCompileTimeType().getRetType();
		return !Types.getTypeVars(args).containsAll(Types.getTypeVars(ret));
	}

	private static boolean isDeclarableTypeSymbol(TypeSymbol sym) {
		if (sym.isAlias()) {
			return false;
		}
		if (sym instanceof BuiltInTypeSymbol) {
			switch ((BuiltInTypeSymbol) sym) {
			case SMT_TYPE:
			case SYM_TYPE:
			case BOOL_TYPE:
			case STRING_TYPE:
			case ARRAY_TYPE:
			case INT_TYPE:
			case MODEL_TYPE:
			case BV:
			case FP:
			case SMT_PATTERN_TYPE:
			case SMT_WRAPPED_VAR_TYPE:
				return false;
			case CMP_TYPE:
			case LIST_TYPE:
			case OPTION_TYPE:
				return true;
			default:
				throw new AssertionError("impossible");
			}
		}
		return true;
	}

}
