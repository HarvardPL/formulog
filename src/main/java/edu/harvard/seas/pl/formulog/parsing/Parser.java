package edu.harvard.seas.pl.formulog.parsing;

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

import static edu.harvard.seas.pl.formulog.util.Util.map;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Constructors;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.FP32;
import edu.harvard.seas.pl.formulog.ast.FP64;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.I32;
import edu.harvard.seas.pl.formulog.ast.I64;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.RelationProperties;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.StringTerm;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.DummyFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDefManager;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogBaseVisitor;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogLexer;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.AdtDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.AggTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.AggTypeListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.AnnotationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.AtomListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.BinopFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.BinopTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ClauseStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ConsTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ConstSymFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ConstructorTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.DisunificationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.DoubleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.FactStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.FloatTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.FormulaTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.FunDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.FunDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.I32TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.I64TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.IfExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.IndexContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.IndexedFunctorContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.IteTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.LetExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.LetFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ListTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.MatchClauseContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.MatchExprContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.NegatedAtomContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.NonEmptyTermListContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.NormalAtomContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.NotFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.OutermostCtorContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ParensTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.PredicateContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.QuantifiedFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.QueryStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.RecordDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.RecordEntryContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.RecordEntryDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.RecordTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.RecordUpdateTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.ReifyTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.RelDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.SpecialFPTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.StringTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TermAtomContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TermSymFormulaContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TupleTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TupleTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TypeAliasContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TypeDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TypeDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TypeDefRHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TypeRefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.TypeVarContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.UnificationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.UninterpFunDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.UninterpSortDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.UnopTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.UnquoteTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogParser.VarTermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.DatalogVisitor;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInPredicateSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.IndexedSymbol;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.SymbolType;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeAlias;
import edu.harvard.seas.pl.formulog.types.TypeManager;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.OpaqueType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.types.Types.TypeVisitor;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class Parser {

	private final SymbolManager symbolManager = new SymbolManager();
	private final TypeManager typeManager = new TypeManager();

	public Parser() {
		symbolManager.initialize();
	}

	private DatalogParser getParser(Reader r) throws ParseException {
		try {
			CharStream chars = CharStreams.fromReader(r);
			DatalogLexer lexer = new DatalogLexer(chars);
			CommonTokenStream tokens = new CommonTokenStream(lexer);
			return new DatalogParser(tokens);
		} catch (IOException e) {
			throw new ParseException(e.getMessage());
		}
	}

	public Pair<Program, Atom> parse(Reader r) throws ParseException {
		return parse(r, Paths.get(""));
	}

	public Pair<Program, Atom> parse(Reader r, Path inputDir) throws ParseException {
		try {
			DatalogParser parser = getParser(r);
			StmtProcessor stmtProcessor = new StmtProcessor(inputDir);
			parser.prog().accept(stmtProcessor);
			return new Pair<>(stmtProcessor.getProgram(), stmtProcessor.getQuery());
		} catch (Exception e) {
			throw new ParseException(e);
		}
	}

	private static List<Integer> getIndices(IndexContext ctx) {
		return map(ctx.INT(), d -> Integer.parseInt(d.getText()));
	}

	private final DatalogVisitor<Type> typeExtractor = new DatalogBaseVisitor<Type>() {

		@Override
		public Type visitTupleType(TupleTypeContext ctx) {
			List<Type> typeArgs = map(ctx.type(), t -> t.accept(this));
			Symbol sym = symbolManager.lookupTupleTypeSymbol(typeArgs.size());
			return AlgebraicDataType.make(sym, typeArgs);
		}

		@Override
		public Type visitTypeVar(TypeVarContext ctx) {
			return TypeVar.get(ctx.getText());
		}

		@Override
		public Type visitTypeRef(TypeRefContext ctx) {
			List<Type> params = map(ctx.type(), t -> t.accept(this));
			String s = ctx.ID().getText();
			List<Integer> indices = getIndices(ctx.index());
			switch (s) {
			case "i32":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type i32 does not have any type parameters.");
				}
				return BuiltInTypes.i32;
			case "i64":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type i64 does not have any type parameters.");
				}
				return BuiltInTypes.i64;
			case "fp32":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type fp32 does not have any type parameters.");
				}
				return BuiltInTypes.fp32;
			case "fp64":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type fp64 does not have any type parameters.");
				}
				return BuiltInTypes.fp64;
			case "string":
				if (params.size() != 0) {
					throw new RuntimeException("Built in type string does not have any type parameters.");
				}
				return BuiltInTypes.string;
			default:
				Pair<Symbol, List<Integer>> p = symbolManager.lookupIndexedSymbol(ctx.ID().getText(), indices);
				Symbol sym = p.fst();
				indices = p.snd();
				params.addAll(map(indices, i -> TypeIndex.make(i)));
				return typeManager.lookup(sym, params);
			}
		}

	};

	private final class StmtProcessor extends DatalogBaseVisitor<Void> {

		private final Map<Symbol, Set<Atom>> initialFacts = new HashMap<>();
		private final Map<Symbol, Set<Rule>> rules = new HashMap<>();
		private final FunctionDefManager functionDefManager = new FunctionDefManager(symbolManager);
		private final FunctionCallFactory functionCallFactory = new FunctionCallFactory(functionDefManager);
		private final Map<Symbol, RelationProperties> relationProperties = new HashMap<>();
		private final Map<Symbol, Pair<AlgebraicDataType, Integer>> recordLabels = new HashMap<>();
		private final Map<Symbol, Symbol[]> constructorLabels = new HashMap<>();
		private final Set<Symbol> externalEdbs = new HashSet<>();
		private final Path inputDir;
		private Atom query;

		public StmtProcessor(Path inputDir) {
			this.inputDir = inputDir;
		}

		@Override
		public Void visitFunDecl(FunDeclContext ctx) {
			List<Pair<Symbol, List<Var>>> ps = map(ctx.funDefLHS(), this::parseFunDefLHS);
			Iterator<Term> bodies = map(ctx.term(), e -> e.accept(termExtractor)).iterator();
			for (Pair<Symbol, List<Var>> p : ps) {
				Symbol sym = p.fst();
				List<Var> args = p.snd();
				Term body = bodies.next();
				functionDefManager.register(CustomFunctionDef.get(sym, args.toArray(new Var[0]), body));
			}
			return null;
		}

		private Pair<Symbol, List<Var>> parseFunDefLHS(FunDefLHSContext ctx) {
			String name = ctx.ID().getText();
			List<Type> argTypes = map(ctx.args.type(), t -> t.accept(typeExtractor));
			Type retType = ctx.retType.accept(typeExtractor);
			Symbol sym = symbolManager.createSymbol(name, argTypes.size(), SymbolType.FUNCTION,
					new FunctorType(argTypes, retType));
			List<Var> args = map(ctx.args.VAR(), x -> Var.get(x.getText()));
			if (args.size() != new HashSet<>(args).size()) {
				throw new RuntimeException(
						"Cannot use the same variable multiple times in a function declaration: " + name);
			}
			return new Pair<>(sym, args);
		}

		List<Type> getRelationTypes(AggTypeListContext ctx) {
			List<Type> types = new ArrayList<>();
			for (Iterator<AggTypeContext> it = ctx.aggType().iterator(); it.hasNext();) {
				AggTypeContext agctx = it.next();
				types.add(agctx.type().accept(typeExtractor));
			}
			return types;
		}

		void getAggregate(AggTypeListContext ctx, RelationProperties props) {
			for (Iterator<AggTypeContext> it = ctx.aggType().iterator(); it.hasNext();) {
				AggTypeContext agctx = it.next();
				if (agctx.func != null) {
					if (it.hasNext()) {
						throw new RuntimeException("Aggregates can only be set for the last column of a relation: "
								+ props.getRelationSymbol());
					}
					Symbol funcSym = symbolManager.lookupSymbol(agctx.func.getText());
					if (!funcSym.getSymbolType().isFunctionSymbol()) {
						throw new RuntimeException("Non-function used in aggregate: " + funcSym);
					}
					Term unit = extract(agctx.unit);
					props.aggregate(funcSym, unit);
				}
			}

		}

		@Override
		public Void visitRelDecl(RelDeclContext ctx) {
			String name = ctx.ID().getText();
			List<Type> types = getRelationTypes(ctx.aggTypeList());
			if (!Types.getTypeVars(types).isEmpty()) {
				throw new RuntimeException("Cannot use type variables in the signature of a relation: " + name);
			}
			SymbolType symType = ctx.relType.getType() == DatalogLexer.OUTPUT ? SymbolType.IDB_REL : SymbolType.EDB_REL;
			Symbol sym = symbolManager.createSymbol(name, types.size(), symType,
					new FunctorType(types, BuiltInTypes.bool));
			RelationProperties props = new RelationProperties(sym);
			getAggregate(ctx.aggTypeList(), props);
			for (AnnotationContext actx : ctx.annotation()) {
				switch (actx.getText()) {
				case "@bottomup":
					if (!sym.getSymbolType().isIDBSymbol()) {
						throw new RuntimeException("Annotation @bottomup not relevant for non-IDB predicate " + sym);
					}
					props.bottomUp();
					break;
				case "@topdown":
					if (!sym.getSymbolType().isIDBSymbol()) {
						throw new RuntimeException("Annotation @bottomup not relevant for non-IDB predicate " + sym);
					}
					props.topDown();
					break;
				case "@external":
					if (!sym.getSymbolType().isEDBSymbol()) {
						throw new RuntimeException("Annotation @external cannot be used for non-EDB predicate " + sym);
					}
					externalEdbs.add(sym);
					break;
				default:
					throw new RuntimeException("Unrecognized annotation for predicate " + sym + ": " + actx.getText());
				}
			}
			relationProperties.put(sym, props);
			if (sym.getSymbolType().isEDBSymbol()) {
				initialFacts.put(sym, new HashSet<>());
			} else {
				rules.put(sym, new HashSet<>());
			}
			return null;
		}

		@Override
		public Void visitTypeAlias(TypeAliasContext ctx) {
			Pair<Symbol, List<TypeVar>> p = parseTypeDefLHS(ctx.typeDefLHS(), SymbolType.TYPE_ALIAS);
			Symbol sym = p.fst();
			List<TypeVar> typeVars = p.snd();
			Type type = ctx.type().accept(typeExtractor);
			if (!typeVars.containsAll(Types.getTypeVars(type))) {
				throw new RuntimeException("Unbound type variable in definition of " + sym);
			}
			typeManager.registerAlias(new TypeAlias(sym, typeVars, type));
			return null;
		}

		@Override
		public Void visitTypeDecl(TypeDeclContext ctx) {
			List<Pair<Symbol, List<TypeVar>>> lhss = map(ctx.typeDefLHS(),
					lhs -> parseTypeDefLHS(lhs, SymbolType.TYPE));
			Iterator<TypeDefRHSContext> it = ctx.typeDefRHS().iterator();
			for (Pair<Symbol, List<TypeVar>> p : lhss) {
				Symbol sym = p.fst();
				List<TypeVar> typeVars = p.snd();
				AlgebraicDataType type = AlgebraicDataType.make(sym, new ArrayList<>(typeVars));
				TypeDefRHSContext rhs = it.next();
				if (rhs.adtDef() != null) {
					handleAdtDef(rhs.adtDef(), type, typeVars);
				} else {
					handleRecordDef(rhs.recordDef(), type, typeVars);
				}
			}
			return null;
		}

		private void handleAdtDef(AdtDefContext ctx, AlgebraicDataType type, List<TypeVar> typeVars) {
			Set<ConstructorScheme> constructors = new HashSet<>();
			for (ConstructorTypeContext ctc : ctx.constructorType()) {
				List<Type> typeArgs = map(ctc.typeList().type(), t -> t.accept(typeExtractor));
				Symbol csym = symbolManager.createSymbol(ctc.ID().getText(), typeArgs.size(),
						SymbolType.VANILLA_CONSTRUCTOR, new FunctorType(typeArgs, type));
				if (!typeVars.containsAll(Types.getTypeVars(typeArgs))) {
					throw new RuntimeException("Unbound type variable in definition of " + csym);
				}
				symbolManager.createSymbol("#is_" + csym.toString(), 1, SymbolType.SOLVER_CONSTRUCTOR_TESTER,
						new FunctorType(type, BuiltInTypes.bool));
				List<Symbol> getterSyms = new ArrayList<>();
				for (int i = 0; i < csym.getArity(); ++i) {
					Type t = new FunctorType(type, typeArgs.get(i));
					String name = "#" + csym.toString() + "_" + (i + 1);
					getterSyms.add(symbolManager.createSymbol(name, 1, SymbolType.SOLVER_CONSTRUCTOR_GETTER, t));
				}
				constructors.add(new ConstructorScheme(csym, typeArgs, getterSyms));
			}
			AlgebraicDataType.setConstructors(type.getSymbol(), typeVars, constructors);
		}

		private void handleRecordDef(RecordDefContext ctx, AlgebraicDataType type, List<TypeVar> typeVars) {
			List<Type> entryTypes = new ArrayList<>();
			List<Symbol> getterSyms = new ArrayList<>();
			List<Symbol> labels = new ArrayList<>();
			int i = 0;
			for (RecordEntryDefContext entry : ctx.recordEntryDef()) {
				Type entryType = entry.type().accept(typeExtractor);
				entryTypes.add(entryType);
				Type labelType = new FunctorType(type, entryType);
				Symbol label = symbolManager.createSymbol(entry.ID().getText(), 1, SymbolType.FUNCTION, labelType);
				labels.add(label);
				final int j = i;
				functionDefManager.register(new FunctionDef() {

					@Override
					public Symbol getSymbol() {
						return label;
					}

					@Override
					public Term evaluate(Term[] args) throws EvaluationException {
						Constructor ctor = (Constructor) args[0];
						return ctor.getArgs()[j];
					}

				});
				Symbol getter = symbolManager.createSymbol("#" + label, 1, SymbolType.SOLVER_CONSTRUCTOR_GETTER,
						labelType);
				getterSyms.add(getter);
				recordLabels.put(label, new Pair<>(type, i));
				i++;
			}
			Symbol sym = type.getSymbol();
			if (!typeVars.containsAll(Types.getTypeVars(entryTypes))) {
				throw new RuntimeException("Unbound type variable in definition of " + sym);
			}
			FunctorType ctype = new FunctorType(entryTypes, type);
			Symbol csym = symbolManager.createSymbol("_rec_" + sym, entryTypes.size(), SymbolType.VANILLA_CONSTRUCTOR,
					ctype);
			ConstructorScheme ctor = new ConstructorScheme(csym, entryTypes, getterSyms);
			AlgebraicDataType.setConstructors(sym, typeVars, Collections.singleton(ctor));
			constructorLabels.put(csym, labels.toArray(new Symbol[0]));
		}

		private Pair<Symbol, List<TypeVar>> parseTypeDefLHS(TypeDefLHSContext ctx, SymbolType symType) {
			List<TypeVar> typeVars = map(ctx.TYPEVAR(), t -> TypeVar.get(t.getText()));
			Symbol sym = symbolManager.createSymbol(ctx.ID().getText(), typeVars.size(), symType, null);
			if (typeVars.size() != (new HashSet<>(typeVars)).size()) {
				throw new RuntimeException(
						"Cannot use the same type variable multiple times in a type declaration: " + sym);
			}
			return new Pair<>(sym, typeVars);
		}

		@Override
		public Void visitUninterpSortDecl(UninterpSortDeclContext ctx) {
			parseTypeDefLHS(ctx.typeDefLHS(), SymbolType.SOLVER_UNINTERPRETED_SORT);
			return null;
		}

		@Override
		public Void visitUninterpFunDecl(UninterpFunDeclContext ctx) {
			ConstructorTypeContext ctc = ctx.constructorType();
			List<Type> typeArgs = map(ctc.typeList().type(), t -> t.accept(typeExtractor));
			Type type = ctx.type().accept(typeExtractor);
			Symbol csym = symbolManager.createSymbol(ctc.ID().getText(), typeArgs.size(),
					SymbolType.SOLVER_UNINTERPRETED_FUNCTION, new FunctorType(typeArgs, type));
			if (!(type instanceof AlgebraicDataType)
					|| !((AlgebraicDataType) type).getSymbol().equals(BuiltInTypeSymbol.SMT_TYPE)) {
				throw new RuntimeException("Uninterpreted function must have an "
						+ BuiltInTypeSymbol.SMT_TYPE.toString() + " type: " + csym);
			}
			if (!Types.getTypeVars(typeArgs).isEmpty() || !Types.getTypeVars(type).isEmpty()) {
				throw new RuntimeException("Unbound type variable in definition of " + csym);
			}
			return null;
		}

		@Override
		public Void visitClauseStmt(ClauseStmtContext ctx) {
			List<Atom> head = atomListContextToAtomList(ctx.clause().head);
			List<Atom> body = atomListContextToAtomList(ctx.clause().body);
			List<BasicRule> newRules = makeRules(head, body);
			for (BasicRule rule : newRules) {
				Symbol sym = rule.getHead().getSymbol();
				if (!sym.getSymbolType().equals(SymbolType.IDB_REL)) {
					throw new RuntimeException("Cannot define a rule for a non-IDB symbol: " + sym);
				}
				Util.lookupOrCreate(rules, sym, () -> new HashSet<>()).add(rule);
			}
			return null;
		}

		private BasicRule makeRule(Atom head, List<Atom> body) {
			List<Atom> newBody = new ArrayList<>(body);
			Atom newHead = removeFuncCallsFromAtom(head, newBody);
			return BasicRule.get(newHead, newBody);
		}

		private List<BasicRule> makeRules(List<Atom> head, List<Atom> body) {
			List<BasicRule> rules = new ArrayList<>();
			for (Atom hd : head) {
				rules.add(makeRule(hd, body));
			}
			return rules;
		}

		private Atom removeFuncCallsFromAtom(Atom a, List<Atom> acc) {
			Term[] args = a.getArgs();
			Term[] newArgs = new Term[args.length];
			for (int i = 0; i < args.length; ++i) {
				newArgs[i] = args[i].visit(new TermVisitor<Void, Term>() {

					@Override
					public Term visit(Var var, Void in) {
						return var;
					}

					@Override
					public Term visit(Constructor constr, Void in) {
						Term[] args = constr.getArgs();
						Term[] newArgs = new Term[args.length];
						for (int i = 0; i < args.length; ++i) {
							newArgs[i] = args[i].visit(this, null);
						}
						return constr.copyWithNewArgs(newArgs);
					}

					@Override
					public Term visit(Primitive<?> prim, Void in) {
						return prim;
					}

					@Override
					public Term visit(Expr expr, Void in) {
						Var x = Var.getFresh();
						acc.add(Atoms.getPositive(BuiltInPredicateSymbol.UNIFY, new Term[] { x, expr }));
						return x;
					}

				}, null);
			}
			return Atoms.get(a.getSymbol(), newArgs, a.isNegated());
		}

		@Override
		public Void visitFactStmt(FactStmtContext ctx) {
			Atom fact = ctx.fact().atom().accept(atomExtractor);
			Symbol sym = fact.getSymbol();
			if (sym.getSymbolType().equals(SymbolType.IDB_REL)) {
				BasicRule rule = makeRule(fact, Collections.emptyList());
				Util.lookupOrCreate(rules, sym, () -> new HashSet<>()).add(rule);
			} else if (sym.getSymbolType().equals(SymbolType.EDB_REL)) {
				Util.lookupOrCreate(initialFacts, sym, () -> new HashSet<>()).add(fact);
			} else {
				throw new RuntimeException("Fact has a non-EDB and non-IDB symbol: " + fact);
			}
			return null;
		}

		@Override
		public Void visitQueryStmt(QueryStmtContext ctx) {
			Atom a = ctx.query().atom().accept(atomExtractor);
			if (query != null) {
				throw new RuntimeException("Cannot have multiple queries in the same program.");
			}
			query = a;
			return null;
		}

		List<Atom> atomListContextToAtomList(AtomListContext ctx) {
			return map(ctx.atom(), a -> a.accept(atomExtractor));
		}

		private Term extract(TermContext ctx) {
			return ctx.accept(termExtractor);
		}

		private final DatalogVisitor<Term> termExtractor = new DatalogBaseVisitor<Term>() {

			public Term extract(TermContext ctx) {
				return ctx.accept(this);
			}

			private boolean inFormula;

			private void assertInFormula(String msg) {
				if (!inFormula) {
					throw new RuntimeException(msg);
				}
			}

			private void assertNotInFormula(String msg) {
				if (inFormula) {
					throw new RuntimeException(msg);
				}
			}

			private void toggleInFormula() {
				inFormula = !inFormula;
			}

			@Override
			public Term visitReifyTerm(ReifyTermContext ctx) {
				Symbol predSym = symbolManager.lookupSymbol(ctx.ID().getText());
				if (!predSym.getSymbolType().isRelationSym()) {
					throw new RuntimeException("Cannot reify something that is not a relation: " + ctx.getText());
				}
				Symbol funcSym = symbolManager.createFunctionSymbolForPredicate(predSym, true);
				if (!functionDefManager.hasDefinition(funcSym)) {
					functionDefManager.register(new DummyFunctionDef(funcSym));
				}
				return functionCallFactory.make(funcSym, Terms.emptyArray());
			}

			@Override
			public Term visitVarTerm(VarTermContext ctx) {
				String var = ctx.VAR().getText();
				if (var.equals("_")) {
					return Var.getFresh();
				}
				return Var.get(ctx.VAR().getText());
			}

			@Override
			public Term visitStringTerm(StringTermContext ctx) {
				String s = ctx.QSTRING().getText();
				return StringTerm.make(s.substring(1, s.length() - 1));
			}

			@Override
			public Term visitConsTerm(ConsTermContext ctx) {
				List<Term> args = map(ctx.term(), t -> t.accept(this));
				return Constructors.make(BuiltInConstructorSymbol.CONS, args.toArray(Terms.emptyArray()));
			}

			@Override
			public Term visitIndexedFunctor(IndexedFunctorContext ctx) {
				Term[] args = termContextsToTerms(ctx.termArgs().term());
				String name = ctx.id.getText();
				List<Integer> indices = getIndices(ctx.index());
				Pair<Symbol, List<Integer>> p = symbolManager.lookupIndexedSymbol(name, indices);
				Symbol sym = p.fst();
				indices = p.snd();
				Term[] expandedArgs = new Term[args.length + indices.size()];
				System.arraycopy(args, 0, expandedArgs, 0, args.length);
				Iterator<Integer> it = indices.iterator();
				for (int i = args.length; i < expandedArgs.length; ++i) {
					Integer idx = it.next();
					Term t;
					if (idx == null) {
						t = Var.getFresh();
					} else {
						Symbol csym = symbolManager.lookupIndexConstructorSymbol(idx);
						t = Constructors.make(csym, Terms.singletonArray(I32.make(idx)));
					}
					expandedArgs[i] = t;
				}
				Term t = makeFunctor(sym, expandedArgs);
				// For a couple constructors, we want to make sure that their arguments are
				// forced to be non-formula types. For example, the constructor bv_const needs
				// to take something of type i32, not i32 expr.
				if (sym instanceof IndexedSymbol) {
					switch ((IndexedSymbol) sym) {
					case BV_BIG_CONST:
					case BV_CONST:
					case FP_BIG_CONST:
					case FP_CONST:
						t = makeExitFormula(t);
					default:
						break;
					}
				}
				return t;
			}

			private Term makeFunctor(Symbol sym, Term[] args) {
				SymbolType st = sym.getSymbolType();
				if (st.isRelationSym()) {
					Symbol newSym = symbolManager.createFunctionSymbolForPredicate(sym, false);
					if (!functionDefManager.hasDefinition(newSym)) {
						functionDefManager.register(new DummyFunctionDef(newSym));
					}
					return functionCallFactory.make(newSym, args);
				} else if (st.isFunctionSymbol()) {
					Term t = functionCallFactory.make(sym, args);
					assertNotInFormula("Cannot invoke a function from within a formula; unquote the call " + t
							+ " by prefacing it with ,");
					return t;
				} else if (st.isConstructorSymbol()) {
					Term t = Constructors.make(sym, args);
					if (st.isSolverConstructorSymbol()) {
						assertInFormula(
								"Can only use an uninterpreted function or solver expression within a formula: " + t);
					}
					return t;
				} else {
					throw new RuntimeException(
							"Cannot create a term with non-constructor, non-function symbol " + sym + ".");
				}
			}

			@Override
			public Term visitTupleTerm(TupleTermContext ctx) {
				Term[] args = termContextsToTerms(ctx.tuple().term());
				return Constructors.make(symbolManager.lookupTupleSymbol(args.length), args);
			}

			private final Pattern hex = Pattern.compile("0x([0-9a-fA-F]+)[lL]?");

			@Override
			public Term visitI32Term(I32TermContext ctx) {
				Matcher m = hex.matcher(ctx.val.getText());
				int n;
				if (m.matches()) {
					n = Integer.parseUnsignedInt(m.group(1).toUpperCase(), 16);
				} else {
					n = Integer.parseInt(ctx.val.getText());
				}
				return I32.make(n);
			}

			@Override
			public Term visitI64Term(I64TermContext ctx) {
				Matcher m = hex.matcher(ctx.val.getText());
				long n;
				if (m.matches()) {
					n = Long.parseUnsignedLong(m.group(1).toUpperCase(), 16);
				} else {
					// Long.parseLong does not allow trailing l or L.
					String text = ctx.val.getText();
					String sub = text.substring(0, text.length() - 1);
					n = Long.parseLong(sub);
				}
				return I64.make(n);
			}

			@Override
			public Term visitFloatTerm(FloatTermContext ctx) {
				return FP32.make(Float.parseFloat(ctx.val.getText()));
			}

			@Override
			public Term visitDoubleTerm(DoubleTermContext ctx) {
				return FP64.make(Double.parseDouble(ctx.val.getText()));
			}

			@Override
			public Term visitSpecialFPTerm(SpecialFPTermContext ctx) {
				switch (ctx.val.getType()) {
				case DatalogParser.FP32_NAN:
					return FP32.make(Float.NaN);
				case DatalogParser.FP32_NEG_INFINITY:
					return FP32.make(Float.NEGATIVE_INFINITY);
				case DatalogParser.FP32_POS_INFINITY:
					return FP32.make(Float.POSITIVE_INFINITY);
				case DatalogParser.FP64_NAN:
					return FP64.make(Double.NaN);
				case DatalogParser.FP64_NEG_INFINITY:
					return FP64.make(Double.NEGATIVE_INFINITY);
				case DatalogParser.FP64_POS_INFINITY:
					return FP64.make(Double.POSITIVE_INFINITY);
				}
				throw new AssertionError();
			}

			@Override
			public Term visitRecordTerm(RecordTermContext ctx) {
				Pair<Symbol, Map<Integer, Term>> p = handleRecordEntries(ctx.recordEntries().recordEntry());
				Symbol csym = p.fst();
				Map<Integer, Term> argMap = p.snd();
				Term[] args = new Term[csym.getArity()];
				if (args.length != argMap.keySet().size()) {
					throw new RuntimeException("Missing label(s) when creating record of type " + csym);
				}
				for (int i = 0; i < args.length; i++) {
					args[i] = argMap.get(i);
				}
				return Constructors.make(csym, args);
			}

			@Override
			public Term visitRecordUpdateTerm(RecordUpdateTermContext ctx) {
				Pair<Symbol, Map<Integer, Term>> p = handleRecordEntries(ctx.recordEntries().recordEntry());
				Symbol csym = p.fst();
				Map<Integer, Term> argMap = p.snd();
				Term[] args = new Term[csym.getArity()];
				Symbol[] labels = constructorLabels.get(csym);
				Term orig = extract(ctx.term());
				for (int i = 0; i < args.length; ++i) {
					Term t = argMap.get(i);
					if (t == null) {
						Symbol label = labels[i];
						t = functionCallFactory.make(label, Terms.singletonArray(orig));
					}
					args[i] = t;
				}
				return Constructors.make(csym, args);
			}

			private Pair<Symbol, Map<Integer, Term>> handleRecordEntries(List<RecordEntryContext> entries) {
				AlgebraicDataType type = null;
				Map<Integer, Term> argMap = new HashMap<>();
				for (RecordEntryContext entry : entries) {
					Symbol label = symbolManager.lookupSymbol(entry.ID().getText());
					Pair<AlgebraicDataType, Integer> p = recordLabels.get(label);
					if (p == null) {
						throw new RuntimeException(label + " is not a record label");
					}
					AlgebraicDataType type2 = p.fst();
					if (type == null) {
						type = type2;
					} else if (!type.equals(type2)) {
						throw new RuntimeException("Cannot use label " + label + " in a record of type " + type);
					}
					if (argMap.putIfAbsent(p.snd(), extract(entry.term())) != null) {
						throw new RuntimeException(
								"Cannot use the same label " + label + " multiple times when creating a record");
					}
				}
				Symbol csym = type.getConstructors().iterator().next().getSymbol();
				return new Pair<>(csym, argMap);
			}

			@Override
			public Term visitUnopTerm(UnopTermContext ctx) {
				Term t = ctx.term().accept(this);
				Symbol sym = tokenToUnopSym(ctx.op.getType());
				if (sym == null) {
					t = makeNonFunctionUnop(ctx.op.getType(), t);
				} else {
					t = functionCallFactory.make(sym, new Term[] { t });
				}
				if (t == null) {
					throw new AssertionError("Unrecognized unop: " + ctx.getText());
				}
				assertNotInFormula("Cannot invoke a unop from within a formula; unquote the operation " + ctx.getText()
						+ " by prefacing it with ,");
				return t;
			}

			private Term makeNonFunctionUnop(int tokenType, Term t) {
				switch (tokenType) {
				case DatalogParser.BANG:
					return makeBoolMatch(t, Constructors.falseTerm(), Constructors.trueTerm());
				default:
					return null;
				}
			}

			private Term makeBoolMatch(Term matchee, Term ifTrue, Term ifFalse) {
				MatchClause matchTrue = MatchClause.make(Constructors.trueTerm(), ifTrue);
				MatchClause matchFalse = MatchClause.make(Constructors.falseTerm(), ifFalse);
				return MatchExpr.make(matchee, Arrays.asList(matchTrue, matchFalse));
			}

			private Symbol tokenToUnopSym(int tokenType) {
				switch (tokenType) {
				case DatalogParser.MINUS:
					return BuiltInFunctionSymbol.I32_NEG;
				default:
					return null;
				}
			}

			private Symbol tokenToBinopSym(int tokenType) {
				switch (tokenType) {
				case DatalogParser.MUL:
					return BuiltInFunctionSymbol.I32_MUL;
				case DatalogParser.DIV:
					return BuiltInFunctionSymbol.I32_DIV;
				case DatalogParser.REM:
					return BuiltInFunctionSymbol.I32_REM;
				case DatalogParser.PLUS:
					return BuiltInFunctionSymbol.I32_ADD;
				case DatalogParser.MINUS:
					return BuiltInFunctionSymbol.I32_SUB;
				case DatalogParser.AMP:
					return BuiltInFunctionSymbol.I32_AND;
				case DatalogParser.CARET:
					return BuiltInFunctionSymbol.I32_XOR;
				case DatalogParser.EQ:
					return BuiltInFunctionSymbol.BEQ;
				case DatalogParser.NEQ:
					return BuiltInFunctionSymbol.BNEQ;
				case DatalogParser.LT:
					return BuiltInFunctionSymbol.I32_LT;
				case DatalogParser.LTE:
					return BuiltInFunctionSymbol.I32_LE;
				case DatalogParser.GT:
					return BuiltInFunctionSymbol.I32_GT;
				case DatalogParser.GTE:
					return BuiltInFunctionSymbol.I32_GE;
				default:
					return null;
				}
			}

			private Term makeNonFunctionBinop(int tokenType, Term lhs, Term rhs) {
				switch (tokenType) {
				case DatalogParser.AMPAMP:
					return makeBoolMatch(lhs, rhs, Constructors.falseTerm());
				case DatalogParser.BARBAR:
					return makeBoolMatch(lhs, Constructors.trueTerm(), rhs);
				default:
					return null;
				}
			}

			@Override
			public Term visitBinopTerm(BinopTermContext ctx) {
				Term[] args = { extract(ctx.term(0)), extract(ctx.term(1)) };
				Symbol sym = tokenToBinopSym(ctx.op.getType());
				Term t;
				if (sym == null) {
					t = makeNonFunctionBinop(ctx.op.getType(), args[0], args[1]);
				} else {
					t = functionCallFactory.make(sym, args);
				}
				if (t == null) {
					throw new AssertionError("Unrecognized binop: " + ctx.getText());
				}
				assertNotInFormula("Cannot invoke a binop from within a formula; unquote the operation " + ctx.getText()
						+ " by prefacing it with ,");
				return t;
			}

			@Override
			public Term visitListTerm(ListTermContext ctx) {
				Term t = Constructors.makeZeroAry(BuiltInConstructorSymbol.NIL);
				List<TermContext> ctxs = new ArrayList<>(ctx.list().term());
				Collections.reverse(ctxs);
				for (TermContext tc : ctxs) {
					t = Constructors.make(BuiltInConstructorSymbol.CONS, new Term[] { extract(tc), t });
				}
				return t;
			}

			@Override
			public Term visitParensTerm(ParensTermContext ctx) {
				return extract(ctx.term());
			}

			private Term makeExitFormula(Term t) {
				return functionCallFactory.make(BuiltInFunctionSymbol.EXIT_FORMULA, Terms.singletonArray(t));
			}

			private Term makeEnterFormula(Term t) {
				return functionCallFactory.make(BuiltInFunctionSymbol.ENTER_FORMULA, Terms.singletonArray(t));
			}

			@Override
			public Term visitUnquoteTerm(UnquoteTermContext ctx) {
				assertInFormula("Can only unquote a term from within a formula. " + ctx.getText());
				toggleInFormula();
				Term t = makeExitFormula(extract(ctx.term()));
				toggleInFormula();
				return t;
			}

			@Override
			public Term visitFormulaTerm(FormulaTermContext ctx) {
				assertNotInFormula("Cannot nest a formula within a formula: " + ctx.getText());
				toggleInFormula();
				Term t = extract(ctx.term());
				t = functionCallFactory.make(BuiltInFunctionSymbol.ENTER_FORMULA, Terms.singletonArray(t));
				toggleInFormula();
				return t;
			}

			@Override
			public Term visitNotFormula(NotFormulaContext ctx) {
				assertInFormula("~ can only be used from within a formula: " + ctx.getText());
				Term t = extract(ctx.term());
				return Constructors.make(BuiltInConstructorSymbol.FORMULA_NOT, Terms.singletonArray(t));
			}

			@Override
			public Term visitBinopFormula(BinopFormulaContext ctx) {
				assertInFormula("Formula binop can only be used from within a formula: " + ctx.getText());
				Term[] args = termContextsToTerms(ctx.term());
				Symbol sym;
				switch (ctx.op.getType()) {
				case DatalogParser.FORMULA_EQ:
				case DatalogParser.IFF:
					sym = BuiltInConstructorSymbol.FORMULA_EQ;
					break;
				case DatalogParser.IMP:
					sym = BuiltInConstructorSymbol.FORMULA_IMP;
					break;
				case DatalogParser.AND:
					sym = BuiltInConstructorSymbol.FORMULA_AND;
					break;
				case DatalogParser.OR:
					sym = BuiltInConstructorSymbol.FORMULA_OR;
					break;
				default:
					throw new AssertionError();
				}
				return Constructors.make(sym, args);
			}

			@Override
			public Term visitLetFormula(LetFormulaContext ctx) {
				assertInFormula("Can only use a let formula within a formula: " + ctx.getText());
				Term[] args = termContextsToTerms(ctx.term());
				args[1] = makeEnterFormula(args[1]);
				args[2] = makeEnterFormula(args[2]);
				return makeExitFormula(Constructors.make(BuiltInConstructorSymbol.FORMULA_LET, args));
			}

			@Override
			public Term visitQuantifiedFormula(QuantifiedFormulaContext ctx) {
				assertInFormula("Can only use a quantified formula within a formula: " + ctx.getText());
				Term[] args = new Term[3];
				args[0] = parseFormulaVarList(ctx.variables);
				args[1] = makeEnterFormula(extract(ctx.boundTerm));
				if (ctx.pattern != null) {
					args[2] = Constructors.make(BuiltInConstructorSymbol.SOME,
							Terms.singletonArray(makeEnterFormula(parseHeterogeneousList(ctx.pattern))));
				} else {
					args[2] = Constructors.makeZeroAry(BuiltInConstructorSymbol.NONE);
				}
				Symbol sym;
				switch (ctx.quantifier.getType()) {
				case DatalogParser.FORALL:
					sym = BuiltInConstructorSymbol.FORMULA_FORALL;
					break;
				case DatalogParser.EXISTS:
					sym = BuiltInConstructorSymbol.FORMULA_EXISTS;
					break;
				default:
					throw new AssertionError();
				}
				return makeExitFormula(Constructors.make(sym, args));
			}

			private Term parseFormulaVarList(NonEmptyTermListContext ctx) {
				return parseNonEmptyTermList(ctx, BuiltInConstructorSymbol.FORMULA_VAR_LIST_NIL,
						BuiltInConstructorSymbol.FORMULA_VAR_LIST_CONS);
			}

			private Term parseHeterogeneousList(NonEmptyTermListContext ctx) {
				return parseNonEmptyTermList(ctx, BuiltInConstructorSymbol.HETEROGENEOUS_LIST_NIL,
						BuiltInConstructorSymbol.HETEROGENEOUS_LIST_CONS);
			}

			private Term parseNonEmptyTermList(NonEmptyTermListContext ctx, Symbol nil, Symbol cons) {
				Term t = Constructors.makeZeroAry(nil);
				List<TermContext> ctxs = new ArrayList<>(ctx.term());
				Collections.reverse(ctxs);
				for (TermContext tc : ctxs) {
					t = Constructors.make(cons, new Term[] { extract(tc), t });
				}
				return t;
			}

			@Override
			public Term visitIteTerm(IteTermContext ctx) {
				Term[] args = termContextsToTerms(ctx.term());
				if (inFormula) {
					return Constructors.make(BuiltInConstructorSymbol.FORMULA_ITE, args);
				} else {
					return makeBoolMatch(args[0], args[1], args[2]);
				}
			}

			@Override
			public Term visitConstSymFormula(ConstSymFormulaContext ctx) {
				Type type = ctx.type().accept(typeExtractor);
				Term id = StringTerm.make(ctx.id.getText().substring(1));
				return extractSolverSymbol(id, type);
			}

			@Override
			public Term visitTermSymFormula(TermSymFormulaContext ctx) {
				Type type = ctx.type().accept(typeExtractor);
				Term id = extract(ctx.term());
				return extractSolverSymbol(id, type);
			}

			private Term extractSolverSymbol(Term id, Type type) {
				type.visit(new TypeVisitor<Void, Void>() {

					@Override
					public Void visit(TypeVar typeVar, Void in) {
						throw new RuntimeException("Cannot create a symbol for parametric type: " + type);
					}

					@Override
					public Void visit(AlgebraicDataType algebraicType, Void in) {
						Symbol sym = algebraicType.getSymbol();
						if (sym.equals(BuiltInTypeSymbol.SMT_TYPE) || sym.equals(BuiltInTypeSymbol.SYM_TYPE)) {
							throw new RuntimeException(
									"Cannot create a symbol with a type that includes expr or sym: " + type);
						}
						for (Type t : algebraicType.getTypeArgs()) {
							t.visit(this, in);
						}
						return null;
					}

					@Override
					public Void visit(OpaqueType opaqueType, Void in) {
						throw new AssertionError();
					}

					@Override
					public Void visit(TypeIndex typeIndex, Void in) {
						return null;
					}

				}, null);
				Symbol sym = symbolManager.lookupSolverSymbol(type);
				return makeExitFormula(Constructors.make(sym, Terms.singletonArray(id)));
			}

			public Term visitOutermostCtor(OutermostCtorContext ctx) {
				Symbol ctor = symbolManager.lookupSymbol(ctx.ID().getText());
				if (!ctor.getSymbolType().isConstructorSymbol()) {
					throw new RuntimeException("Cannot use non-constructor symbol " + ctor + " in a `not` term.");
				}

				// we'll call a fixed function name
				FunctorType ctorType = (FunctorType) ctor.getCompileTimeType();
				String name = "not%" + ctor;
				Symbol isNotFun;
				if (symbolManager.hasSymbol(name)) {
					isNotFun = symbolManager.lookupSymbol(name);
				} else {
					isNotFun = symbolManager.createSymbol("not%" + ctor, 1, SymbolType.FUNCTION,
							new FunctorType(ctorType.getRetType(), BuiltInTypes.bool));
				}

				// generate the function if needed
				if (!functionDefManager.hasDefinition(isNotFun)) {
					functionDefManager.register(new FunctionDef() {

						@Override
						public Symbol getSymbol() {
							return isNotFun;
						}

						@Override
						public Term evaluate(Term[] args) throws EvaluationException {
							Constructor c = (Constructor) args[0];
							if (c.getSymbol().equals(ctor)) {
								return Constructors.falseTerm();
							}
							return Constructors.trueTerm();
						}

					});
				}

				Term arg = extract(ctx.term());
				return functionCallFactory.make(isNotFun, Terms.singletonArray(arg));
			}

			@Override
			public Term visitMatchExpr(MatchExprContext ctx) {
				Term guard = ctx.term().accept(this);
				List<MatchClause> matches = new ArrayList<>();
				for (MatchClauseContext mcc : ctx.matchClause()) {
					Term rhs = extract(mcc.rhs);
					for (TermContext pc : mcc.patterns().term()) {
						Term pattern = extract(pc);
						matches.add(MatchClause.make(pattern, rhs));
					}
				}
				return MatchExpr.make(guard, matches);
			}

			@Override
			public Term visitLetExpr(LetExprContext ctx) {
				List<Term> ts = map(ctx.letBind().term(), StmtProcessor.this::extract);
				Term t;
				if (ts.size() > 1) {
					t = Constructors.make(symbolManager.lookupTupleSymbol(ts.size()), ts.toArray(Terms.emptyArray()));
				} else {
					t = ts.get(0);
				}
				Term assign = ctx.assign.accept(this);
				Term body = ctx.body.accept(this);
				MatchClause m = MatchClause.make(t, body);
				return MatchExpr.make(assign, Collections.singletonList(m));
			}

			@Override
			public Term visitIfExpr(IfExprContext ctx) {
				Term guard = ctx.guard.accept(this);
				Term thenExpr = ctx.thenExpr.accept(this);
				Term elseExpr = ctx.elseExpr.accept(this);
				List<MatchClause> branches = new ArrayList<>();
				branches.add(MatchClause.make(Constructors.trueTerm(), thenExpr));
				branches.add(MatchClause.make(Constructors.falseTerm(), elseExpr));
				return MatchExpr.make(guard, branches);
			}

		};

		private Term[] termContextsToTerms(List<TermContext> ctxs) {
			return map(ctxs, this::extract).toArray(Terms.emptyArray());
		}

		private final DatalogVisitor<Atom> atomExtractor = new DatalogBaseVisitor<Atom>() {

			private Atom extractAtom(PredicateContext ctx, boolean negated) {
				Term[] args = termContextsToTerms(ctx.termArgs().term());
				Symbol sym = symbolManager.lookupSymbol(ctx.ID().getText());
				SymbolType symType = sym.getSymbolType();
				if (symType.isFunctionSymbol()) {
					Term f = functionCallFactory.make(sym, args);
					return Atoms.liftTerm(f, negated);
				}
				if (symType.isConstructorSymbol()) {
					Term c = Constructors.make(sym, args);
					return Atoms.liftTerm(c, negated);
				}
				if (symType.isRelationSym()) {
					return Atoms.get(sym, args, negated);
				}
				throw new AssertionError("impossible");
			}

			@Override
			public Atom visitNormalAtom(NormalAtomContext ctx) {
				return extractAtom(ctx.predicate(), false);
			}

			@Override
			public Atom visitNegatedAtom(NegatedAtomContext ctx) {
				return extractAtom(ctx.predicate(), true);
			}

			@Override
			public Atom visitUnification(UnificationContext ctx) {
				Term[] args = termContextsToTerms(ctx.term());
				return Atoms.getPositive(BuiltInPredicateSymbol.UNIFY, args);
			}

			@Override
			public Atom visitDisunification(DisunificationContext ctx) {
				Term[] args = termContextsToTerms(ctx.term());
				return Atoms.getNegated(BuiltInPredicateSymbol.UNIFY, args);
			}

			@Override
			public Atom visitTermAtom(TermAtomContext ctx) {
				Term arg = extract(ctx.term());
				return Atoms.getPositive(BuiltInPredicateSymbol.UNIFY,
						new Term[] { arg, Constructors.makeZeroAry(BuiltInConstructorSymbol.TRUE) });
			}

		};

		public Atom getQuery() {
			return query;
		}

		private void readEdbFromFile(Symbol sym) throws ParseException {
			Set<Atom> facts = Util.lookupOrCreate(initialFacts, sym, () -> new HashSet<>());
			Path path = inputDir.resolve(sym.toString() + ".csv");
			try {
				Stream<String> lines;
				lines = Files.lines(path);
				for (Iterator<String> it = lines.iterator(); it.hasNext();) {
					readLineFromCsv(sym, new StringReader(it.next()), facts);
				}
				lines.close();
			} catch (Exception e) {
				throw new ParseException("Exception when extracting facts from " + path + ":\n" + e);
			}
		}

		private void readLineFromCsv(Symbol sym, Reader r, Set<Atom> facts) throws ParseException {
			DatalogParser parser = getParser(r);
			Term[] args = new Term[sym.getArity()];
			for (int i = 0; i < args.length; i++) {
				args[i] = extract(parser.term());
			}
			Atom fact = Atoms.getPositive(sym, args);
			facts.add(fact);
		}

		public Program getProgram() throws ParseException {
			for (Symbol sym : externalEdbs) {
				readEdbFromFile(sym);
			}
			return new Program() {

				@Override
				public Set<Symbol> getFunctionSymbols() {
					return functionDefManager.getFunctionSymbols();
				}

				@Override
				public Set<Symbol> getFactSymbols() {
					return Collections.unmodifiableSet(initialFacts.keySet());
				}

				@Override
				public Set<Symbol> getRuleSymbols() {
					return Collections.unmodifiableSet(rules.keySet());
				}

				@Override
				public FunctionDef getDef(Symbol sym) {
					assert sym.getSymbolType().isFunctionSymbol();
					return functionDefManager.lookup(sym);
				}

				@Override
				public Set<Atom> getFacts(Symbol sym) {
					assert sym.getSymbolType().isEDBSymbol();
					return Util.lookupOrCreate(initialFacts, sym, () -> Collections.emptySet());
				}

				@Override
				public Set<Rule> getRules(Symbol sym) {
					assert sym.getSymbolType().isIDBSymbol();
					return Util.lookupOrCreate(rules, sym, () -> Collections.emptySet());
				}

				@Override
				public SymbolManager getSymbolManager() {
					return symbolManager;
				}

				@Override
				public RelationProperties getRelationProperties(Symbol sym) {
					assert sym.getSymbolType().isRelationSym();
					return Util.lookupOrCreate(relationProperties, sym, () -> new RelationProperties(sym));
				}

			};
		}
	};

}
