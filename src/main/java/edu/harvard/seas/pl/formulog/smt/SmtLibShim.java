package edu.harvard.seas.pl.formulog.smt;

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

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
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
import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector;
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
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.smt.SmtLibParser.SmtLibParseException;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
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

	private final BufferedReader in;
	private PrintWriter out;
	private final Map<SolverVariable, String> declaredSymbols = new HashMap<>();
	private final Deque<Set<SolverVariable>> symbolsByStackPos = new ArrayDeque<>();
	private final Map<String, SolverVariable> symbolLookup = new HashMap<>();
	private PrintWriter log;
	private Iterator<Pair<ConstructorSymbol, Type>> typeAnnotations;

	private SymbolManager symbolManager;
	private final List<String> declarations = new ArrayList<>();

	public SmtLibShim(Reader in, Writer out) {
		this(in, out, null);
	}

	public SmtLibShim(Reader in, Writer out, Writer log) {
		this.in = in != null ? new BufferedReader(in) : null;
		this.out = new PrintWriter(out);
		this.log = log != null ? new PrintWriter(log) : null;
		symbolsByStackPos.add(new HashSet<>());
	}

	public void initialize(Program<?, ?> prog, boolean declareAdts) {
		symbolManager = prog.getSymbolManager();
		new DeclarationGatherer(declareAdts).go(prog);
		if (Configuration.smtCheckSuccess) {
			println("(set-option :print-success true)");
		}
		flush();
		try {
			checkSuccess();
		} catch (EvaluationException e) {
			throw new AssertionError(e);
		}
	}

	private void checkSuccess() throws EvaluationException {
		if (in != null && Configuration.smtCheckSuccess) {
			try {
				String r = in.readLine();
				if (log != null) {
					log.println("; success? " + r);
					log.flush();
				}
				if (r == null || !r.equals("success")) {
					throw new EvaluationException("Solver did not return success: " + r);
				}
			} catch (IOException e) {
				throw new EvaluationException("Problem with evaluating solver: " + e.getMessage());
			}
		}
	}

	public void makeAssertion(SmtLibTerm assertion) throws EvaluationException {
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
		flush();
		checkSuccess();
		if (recordTime) {
			end = System.currentTimeMillis();
			Configuration.recordSmtSerialTime(end - start);
		}
		assert !typeAnnotations.hasNext() : typeAnnotations.next();
		flush();
	}

	public void reset() throws EvaluationException {
		declaredSymbols.clear();
		symbolLookup.clear();
		symbolsByStackPos.clear();
		symbolsByStackPos.add(new HashSet<>());
		println("(reset)");
		flush();
		checkSuccess();
	}

	public void push() throws EvaluationException {
		println("(push 1)");
		flush();
		checkSuccess();
		symbolsByStackPos.addLast(new HashSet<>());
	}

	public void pop() throws EvaluationException {
		println("(pop 1)");
		flush();
		checkSuccess();
		for (SolverVariable x : symbolsByStackPos.removeLast()) {
			String s = declaredSymbols.remove(x);
			symbolLookup.remove(s);
		}
	}

	public SmtStatus checkSat(int timeout) throws EvaluationException {
		return checkSatAssuming(Collections.emptyList(), Collections.emptyList(), timeout);
	}

	public SmtStatus checkSatAssuming(Collection<SolverVariable> onVars, Collection<SolverVariable> offVars,
			int timeout) throws EvaluationException {
		if (timeout < 0) {
			System.err.println("Warning: negative timeout provided to solver - ignored");
			timeout = Integer.MAX_VALUE;
		}
		if (Configuration.smtSolver.equals("z3")) {
			println("(set-option :timeout " + timeout + ")");
			flush();
			checkSuccess();
		}
		if (onVars.isEmpty() && offVars.isEmpty()) {
			println("(check-sat)");
		} else {
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
		}
		flush();
		String result;
		try {
			result = in.readLine();
			if (result == null) {
				throw new EvaluationException("Problem with evaluating solver! Unexpected end of stream");
			}
			if (log != null) {
				log.println("; result: " + result);
				log.flush();
			}
			if (result.equals("sat")) {
				return SmtStatus.SATISFIABLE;
			} else if (result.equals("unsat")) {
				return SmtStatus.UNSATISFIABLE;
			} else if (result.equals("unknown")) {
				return SmtStatus.UNKNOWN;
			} else {
				throw new EvaluationException("Problem with evaluating solver! Unexpected result: " + result);
			}
		} catch (IOException e) {
			throw new EvaluationException("Problem with evaluating solver: " + e.getMessage());
		}
	}

	public Map<SolverVariable, Term> getModel() throws EvaluationException {
		println("(get-model)");
		flush();
		try {
			return parseModel();
		} catch (IOException e) {
			throw new EvaluationException("Problem with evaluating solver: " + e.getMessage());
		} catch (SmtLibParseException e) {
			throw new EvaluationException("Problem parsing solver output: " + e.getMessage());
		}
	}

	public Map<SolverVariable, Term> parseModel() throws EvaluationException, IOException, SmtLibParseException {
		SmtLibParser p = new SmtLibParser(symbolManager, symbolLookup);
		return p.getModel(in);
	}

	public void flush() {
		out.flush();
		if (log != null) {
			log.flush();
		}
	}

	public void setLogic(String logic) throws EvaluationException {
		println("(set-logic " + logic + ")");
		flush();
		checkSuccess();
	}

	public void print(String s) {
		out.print(s);
		if (log != null) {
			log.print(s);
			log.flush();
		}
	}

	private void println(String s) {
		print(s);
		print("\n");
	}

	public void printComment(String comment) {
		println("; " + comment);
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

	private String toSmtSymbol(SolverVariable x) {
		return "x" + x.getId();
	}

	private void declareSymbols(SmtLibTerm t) throws EvaluationException {
		t.accept(new TermVisitorExn<Void, Void, EvaluationException>() {

			@Override
			public Void visit(Var t, Void in) {
				throw new AssertionError("impossible");
			}

			@Override
			public Void visit(Constructor c, Void in) throws EvaluationException {
				if (c instanceof SolverVariable) {
					SolverVariable var = (SolverVariable) c;
					if (!declaredSymbols.containsKey(var)) {
						String s = toSmtSymbol(var);
						declaredSymbols.put(var, s);
						symbolLookup.put(s, var);
						symbolsByStackPos.getLast().add(var);
						print("(declare-fun " + s + " () ");
						FunctorType ft = (FunctorType) var.getSymbol().getCompileTimeType();
						print(stringifyType(ft.getRetType()));
						println(")");
						flush();
						checkSuccess();
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

	public void makeDeclarations() {
		for (String decl : declarations) {
			println(decl);
			flush();
			try {
				checkSuccess();
			} catch (EvaluationException e) {
				System.err.println("WARNING: solver rejected declaration:\n" + decl + "\n" + e.getMessage());
			}
		}
	}

	private class DeclarationGatherer {

		private final ByteArrayOutputStream baos = new ByteArrayOutputStream();
		private final boolean declareAdts;

		public DeclarationGatherer(boolean declareAdts) {
			this.declareAdts = declareAdts;
		}

		public void go(Program<?, ?> prog) {
			PrintWriter tmpLog = log;
			log = null;
			PrintWriter tmpOut = out;
			out = new PrintWriter(baos);
			declareSorts(prog.getTypeSymbols());
			declareUninterpretedFunctions(prog.getUninterpretedFunctionSymbols());
			out = tmpOut;
			log = tmpLog;
		}

		private void pushDeclaration() {
			flush();
			declarations.add(baos.toString());
			baos.reset();
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
				print(") " + stringifyType(ft.getRetType()) + ")");
				pushDeclaration();
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
			} else if (declareAdts) {
				assert sym.isNormalType();
				declareAdtSorts(sorts);
			}
		}

		private void declareUninterpretedSort(TypeSymbol sort) {
			assert sort.isUninterpretedSort();
			print("(declare-sort " + stringifySymbol(sort) + " " + sort.getArity() + ")");
			pushDeclaration();
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
			print("))");
			pushDeclaration();
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

		private boolean isDeclarableTypeSymbol(TypeSymbol sym) {
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
					if (needsTypeAnnotation(sym)) {
						types.add(new Pair<>(sym, ty));
					}
					if (!(c instanceof SolverVariable)) {
						Iterator<Type> it = ft.getArgTypes().iterator();
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

	public static boolean needsTypeAnnotation(ConstructorSymbol sym) {
		if (sym.getConstructorSymbolType().equals(ConstructorSymbolType.VANILLA_CONSTRUCTOR)) {
			return true;
		}
		FunctorType ft = sym.getCompileTimeType();
		List<Type> args = ft.getArgTypes();
		Type ret = sym.getCompileTimeType().getRetType();
		return !Types.getTypeVars(args).containsAll(Types.getTypeVars(ret));
	}

}
