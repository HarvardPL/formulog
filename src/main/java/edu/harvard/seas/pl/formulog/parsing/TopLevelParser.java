package edu.harvard.seas.pl.formulog.parsing;

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


import static edu.harvard.seas.pl.formulog.util.Util.map;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.ComplexLiterals;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.functions.RecordAccessor;
import edu.harvard.seas.pl.formulog.functions.UserFunctionDef;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogBaseVisitor;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogLexer;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AdtDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.AnnotationContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ClauseStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ConstructorTypeContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FactStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.FunDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.ProgContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.QueryStmtContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RecordEntryDefContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.RelDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TermContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeAliasContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeDefLHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.TypeDefRHSContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UninterpFunDeclContext;
import edu.harvard.seas.pl.formulog.parsing.generated.FormulogParser.UninterpSortDeclContext;
import edu.harvard.seas.pl.formulog.symbols.BuiltInFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.BuiltInTypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbolType;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.MutableRelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.RecordSymbol;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.symbols.SymbolManager;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbol;
import edu.harvard.seas.pl.formulog.symbols.TypeSymbolType;
import edu.harvard.seas.pl.formulog.types.BuiltInTypes;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.TypeAlias;
import edu.harvard.seas.pl.formulog.types.Types;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType.ConstructorScheme;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeVar;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

class TopLevelParser {

	private final ParsingContext pc;
	
	public TopLevelParser(ParsingContext parsingContext) {
		pc = parsingContext;
	}
	
	public Pair<BasicProgram, Set<RelationSymbol>> parse(ProgContext ctx) throws ParseException {
		TopLevelVisitor visitor = new TopLevelVisitor();
		ctx.accept(visitor);
		BasicProgram prog = visitor.program();
		return new Pair<>(prog, visitor.externalEdbs);
	}
	
	private final class TopLevelVisitor extends FormulogBaseVisitor<Void> {
		
		private final VariableCheckPass varChecker = new VariableCheckPass(pc.symbolManager());
		private final TermExtractor termExtractor = new TermExtractor(pc);
		private final TypeExtractor typeExtractor = new TypeExtractor(pc);
		private final Map<RelationSymbol, Set<Term[]>> initialFacts = new HashMap<>();
		private final Map<RelationSymbol, Set<BasicRule>> rules = new HashMap<>();
		private final Set<RelationSymbol> externalEdbs = new HashSet<>();
		private final Set<ConstructorSymbol> uninterpFuncSymbols = new HashSet<>();
		private UserPredicate query;

		@Override
		public Void visitFunDecl(FunDeclContext ctx) {
			List<Pair<FunctionSymbol, List<Var>>> ps = ParsingUtil.extractFunDeclarations(pc, ctx.funDefs().funDefLHS(), false);
			Iterator<Term> bodies = termExtractor.extractList(ctx.funDefs().term()).iterator();
			for (Pair<FunctionSymbol, List<Var>> p : ps) {
				FunctionSymbol sym = p.fst();
				List<Var> args = p.snd();
				Term body = bodies.next();
				try {
					Term newBody = varChecker.checkFunction(args, body);
					pc.functionDefManager().register(UserFunctionDef.get(sym, args, newBody));
				} catch (ParseException e) {
					throw new RuntimeException(
							"Error in definition for function " + sym + ": " + e.getMessage() + "\n" + body);
				}
			}
			return null;
		}

		@Override
		public Void visitRelDecl(RelDeclContext ctx) {
			String name = ctx.ID().getText();
			List<Type> types = typeExtractor.extract(ctx.typeList().type());
			if (!Types.getTypeVars(types).isEmpty()) {
				throw new RuntimeException("Cannot use type variables in the signature of a relation: " + name);
			}
			boolean isIdb = ctx.relType.getType() == FormulogLexer.OUTPUT;
			MutableRelationSymbol sym = pc.symbolManager().createRelationSymbol(name, types.size(), isIdb,
					new FunctorType(types, BuiltInTypes.bool));
			for (AnnotationContext actx : ctx.annotation()) {
				switch (actx.getText()) {
				case "@bottomup":
					if (!sym.isIdbSymbol()) {
						throw new RuntimeException("Annotation @bottomup not relevant for non-IDB predicate " + sym);
					}
					sym.setBottomUp();
					break;
				case "@topdown":
					if (!sym.isIdbSymbol()) {
						throw new RuntimeException("Annotation @bottomup not relevant for non-IDB predicate " + sym);
					}
					sym.setTopDown();
					break;
				case "@external":
					if (!sym.isEdbSymbol()) {
						throw new RuntimeException("Annotation @external cannot be used for non-EDB predicate " + sym);
					}
					externalEdbs.add(sym);
					sym.setExternal();
					break;
				default:
					throw new RuntimeException("Unrecognized annotation for predicate " + sym + ": " + actx.getText());
				}
			}
			if (sym.isEdbSymbol()) {
				initialFacts.put(sym, Util.concurrentSet());
			} else {
				rules.put(sym, new HashSet<>());
			}
			return null;
		}

		@Override
		public Void visitTypeAlias(TypeAliasContext ctx) {
			Pair<TypeSymbol, List<TypeVar>> p = parseTypeDefLHS(ctx.typeDefLHS(), TypeSymbolType.TYPE_ALIAS);
			TypeSymbol sym = p.fst();
			List<TypeVar> typeVars = p.snd();
			Type type = typeExtractor.extract(ctx.type());
			if (!typeVars.containsAll(Types.getTypeVars(type))) {
				throw new RuntimeException("Unbound type variable in definition of " + sym);
			}
			pc.typeManager().registerAlias(new TypeAlias(sym, typeVars, type));
			return null;
		}

		@Override
		public Void visitTypeDecl(TypeDeclContext ctx) {
			List<Pair<TypeSymbol, List<TypeVar>>> lhss = map(ctx.typeDefLHS(),
					lhs -> parseTypeDefLHS(lhs, TypeSymbolType.NORMAL_TYPE));
			Iterator<TypeDefRHSContext> it = ctx.typeDefRHS().iterator();
			for (Pair<TypeSymbol, List<TypeVar>> p : lhss) {
				TypeSymbol sym = p.fst();
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
				List<Type> typeArgs = typeExtractor.extract(ctc.typeList().type());
				ConstructorSymbol csym = pc.symbolManager().createConstructorSymbol(ctc.ID().getText(), typeArgs.size(),
						ConstructorSymbolType.VANILLA_CONSTRUCTOR, new FunctorType(typeArgs, type));
				if (!typeVars.containsAll(Types.getTypeVars(typeArgs))) {
					throw new RuntimeException("Unbound type variable in definition of " + csym);
				}
				pc.symbolManager().createConstructorSymbol("#is_" + csym.toString(), 1,
						ConstructorSymbolType.SOLVER_CONSTRUCTOR_TESTER, new FunctorType(type, BuiltInTypes.bool));
				List<ConstructorSymbol> getterSyms = new ArrayList<>();
				for (int i = 0; i < csym.getArity(); ++i) {
					FunctorType t = new FunctorType(type, typeArgs.get(i));
					String name = "#" + csym.toString() + "_" + (i + 1);
					getterSyms.add(pc.symbolManager().createConstructorSymbol(name, 1,
							ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER, t));
				}
				constructors.add(new ConstructorScheme(csym, typeArgs, getterSyms));
			}
			AlgebraicDataType.setConstructors(type.getSymbol(), typeVars, constructors);
		}

		private void handleRecordDef(RecordDefContext ctx, AlgebraicDataType type, List<TypeVar> typeVars) {
			List<Type> entryTypes = new ArrayList<>();
			List<ConstructorSymbol> getterSyms = new ArrayList<>();
			List<FunctionSymbol> labels = new ArrayList<>();
			int i = 0;
			for (RecordEntryDefContext entry : ctx.recordEntryDef()) {
				Type entryType = typeExtractor.extract(entry.type());
				entryTypes.add(entryType);
				FunctorType labelType = new FunctorType(type, entryType);
				FunctionSymbol label = pc.symbolManager().createFunctionSymbol(entry.ID().getText(), 1, labelType);
				labels.add(label);
				final int j = i;
				pc.functionDefManager().register(new RecordAccessor(label, j));
				ConstructorSymbol getter = pc.symbolManager().createConstructorSymbol("#" + label, 1,
						ConstructorSymbolType.SOLVER_CONSTRUCTOR_GETTER, labelType);
				getterSyms.add(getter);
				pc.recordLabels().put(label, new Pair<>(type, i));
				i++;
			}
			TypeSymbol sym = type.getSymbol();
			if (!typeVars.containsAll(Types.getTypeVars(entryTypes))) {
				throw new RuntimeException("Unbound type variable in definition of " + sym);
			}
			FunctorType ctype = new FunctorType(entryTypes, type);
			RecordSymbol csym = pc.symbolManager().createRecordSymbol("_rec_" + sym, entryTypes.size(), ctype, labels);
			ConstructorScheme ctor = new ConstructorScheme(csym, entryTypes, getterSyms);
			AlgebraicDataType.setConstructors(sym, typeVars, Collections.singleton(ctor));
			pc.constructorLabels().put(csym, labels.toArray(new FunctionSymbol[0]));
		}

		private Pair<TypeSymbol, List<TypeVar>> parseTypeDefLHS(TypeDefLHSContext ctx, TypeSymbolType symType) {
			List<TypeVar> typeVars = map(ctx.TYPEVAR(), t -> TypeVar.get(t.getText()));
			TypeSymbol sym = pc.symbolManager().createTypeSymbol(ctx.ID().getText(), typeVars.size(), symType);
			if (typeVars.size() != (new HashSet<>(typeVars)).size()) {
				throw new RuntimeException(
						"Cannot use the same type variable multiple times in a type declaration: " + sym);
			}
			return new Pair<>(sym, typeVars);
		}

		@Override
		public Void visitUninterpSortDecl(UninterpSortDeclContext ctx) {
			parseTypeDefLHS(ctx.typeDefLHS(), TypeSymbolType.UNINTERPRETED_SORT);
			return null;
		}

		@Override
		public Void visitUninterpFunDecl(UninterpFunDeclContext ctx) {
			ConstructorTypeContext ctc = ctx.constructorType();
			List<Type> typeArgs = typeExtractor.extract(ctc.typeList().type());
			Type type = typeExtractor.extract(ctx.type());
			ConstructorSymbol csym = pc.symbolManager().createConstructorSymbol(ctc.ID().getText(), typeArgs.size(),
					ConstructorSymbolType.SOLVER_UNINTERPRETED_FUNCTION, new FunctorType(typeArgs, type));
			Set<Type> allTypes = new HashSet<>(typeArgs);
			allTypes.add(type);
			for (Type ty : allTypes) {
				if (!hasSmtType(ty)) {
					throw new RuntimeException("Uninterpreted function must have an "
							+ BuiltInTypeSymbol.SMT_TYPE.toString() + " type: " + csym);
				}
				if (!Types.getTypeVars(ty).isEmpty()) {
					throw new RuntimeException("Uninterpreted functions cannot have type variables: " + csym);
				}
			}
			uninterpFuncSymbols.add(csym);
			return null;
		}

		private boolean hasSmtType(Type type) {
			return (type instanceof AlgebraicDataType)
					&& ((AlgebraicDataType) type).getSymbol().equals(BuiltInTypeSymbol.SMT_TYPE);

		}

		@Override
		public Void visitClauseStmt(ClauseStmtContext ctx) {
			List<ComplexLiteral> head = termsToLiterals(ctx.clause().head.term());
			List<ComplexLiteral> body = termsToLiterals(ctx.clause().body.term());
			List<BasicRule> newRules = makeRules(head, body);
			for (BasicRule rule : newRules) {
				RelationSymbol sym = rule.getHead().getSymbol();
				if (!sym.isIdbSymbol()) {
					throw new RuntimeException("Cannot define a rule for a non-IDB symbol: " + sym);
				}
				Util.lookupOrCreate(rules, sym, () -> new HashSet<>()).add(rule);
			}
			return null;
		}

		private BasicRule makeRule(ComplexLiteral head, List<ComplexLiteral> body) {
			List<ComplexLiteral> newBody = new ArrayList<>(body);
			if (!(head instanceof UserPredicate)) {
				throw new RuntimeException("Cannot create rule with non-user predicate in head: " + head);
			}
			try {
				return varChecker.checkRule((BasicRule.make((UserPredicate) head, newBody)));
			} catch (ParseException e) {
				throw new RuntimeException(e);
			}
		}

		private List<BasicRule> makeRules(List<ComplexLiteral> head, List<ComplexLiteral> body) {
			List<BasicRule> rules = new ArrayList<>();
			for (ComplexLiteral hd : head) {
				rules.add(makeRule(hd, body));
			}
			return rules;
		}

		@Override
		public Void visitFactStmt(FactStmtContext ctx) {
			ComplexLiteral lit = termToLiteral(ctx.fact().term());
			if (!(lit instanceof UserPredicate)) {
				throw new RuntimeException("Facts must be user-defined predicates: " + ctx.getText());
			}
			UserPredicate fact = (UserPredicate) lit;
			RelationSymbol sym = fact.getSymbol();
			if (sym.isIdbSymbol()) {
				BasicRule rule = makeRule(fact, Collections.emptyList());
				rules.get(sym).add(rule);
			} else {
				try {
					Term[] args = varChecker.checkFact(fact.getArgs());
					initialFacts.get(sym).add(args);
				} catch (ParseException e) {
					throw new RuntimeException(e);
				}
			}
			return null;
		}

		@Override
		public Void visitQueryStmt(QueryStmtContext ctx) {
			ComplexLiteral a = termToLiteral(ctx.query().term());
			if (!(a instanceof UserPredicate)) {
				throw new RuntimeException("Query must be for a user-defined predicate: " + a);
			}
			if (query != null) {
				throw new RuntimeException("Cannot have multiple queries in the same program: " + query + " and " + a);
			}
			UserPredicate q = (UserPredicate) a;
			try {
				query = UserPredicate.make(q.getSymbol(), varChecker.checkFact(q.getArgs()), q.isNegated());
			} catch (ParseException e) {
				throw new RuntimeException("Problem with query " + query + ": " + e.getMessage());
			}
			return null;
		}

		List<ComplexLiteral> termsToLiterals(Iterable<TermContext> ctxs) {
			List<ComplexLiteral> l = new ArrayList<>();
			for (TermContext ctx : ctxs) {
				l.add(termToLiteral(ctx));
			}
			return l;
		}
		
		private ComplexLiteral termToLiteral(TermContext ctx) {
			Term t = termExtractor.extract(ctx);
			if (!(t instanceof FunctionCall)) {
				return ComplexLiterals.unifyWithBool(t, true);
			}
			FunctionCall call = (FunctionCall) t;
			FunctionSymbol sym = call.getSymbol();
			boolean negated = false;
			if (sym.equals(BuiltInFunctionSymbol.BNOT)) {
				t = call.getArgs()[0];
				if (!(t instanceof FunctionCall)) {
					return ComplexLiterals.unifyWithBool(t, false);
				}
				negated = true;
				call = (FunctionCall) t;
				sym = call.getSymbol();
			}
			if (sym instanceof PredicateFunctionSymbol) {
				RelationSymbol predSym = ((PredicateFunctionSymbol) sym).getPredicateSymbol();
				return UserPredicate.make(predSym, call.getArgs(), negated);
			}
			if (!negated && sym.equals(BuiltInFunctionSymbol.BEQ)) {
				Term[] args = call.getArgs();
				return UnificationPredicate.make(args[0], args[1], false);
			}
			if (!negated && sym.equals(BuiltInFunctionSymbol.BNEQ)) {
				Term[] args = call.getArgs();
				return UnificationPredicate.make(args[0], args[1], true);
			}
			return ComplexLiterals.unifyWithBool(t, !negated);
		}
		
		public BasicProgram program() throws ParseException {
			return new BasicProgram() {

				@Override
				public Set<FunctionSymbol> getFunctionSymbols() {
					return pc.functionDefManager().getFunctionSymbols();
				}

				@Override
				public Set<RelationSymbol> getFactSymbols() {
					return Collections.unmodifiableSet(new HashSet<>(initialFacts.keySet()));
				}

				@Override
				public Set<RelationSymbol> getRuleSymbols() {
					return Collections.unmodifiableSet(new HashSet<>(rules.keySet()));
				}

				@Override
				public FunctionDef getDef(FunctionSymbol sym) {
					return pc.functionDefManager().lookup(sym);
				}

				@Override
				public Set<Term[]> getFacts(RelationSymbol sym) {
					if (!sym.isEdbSymbol()) {
						throw new IllegalArgumentException();
					}
					if (!initialFacts.containsKey(sym)) {
						throw new IllegalArgumentException();
					}
					return initialFacts.get(sym);
				}

				@Override
				public Set<BasicRule> getRules(RelationSymbol sym) {
					if (!sym.isIdbSymbol()) {
						throw new IllegalArgumentException();
					}
					if (!rules.containsKey(sym)) {
						throw new IllegalArgumentException();
					}
					return rules.get(sym);
				}

				@Override
				public SymbolManager getSymbolManager() {
					return pc.symbolManager();
				}

				@Override
				public boolean hasQuery() {
					return query != null;
				}

				@Override
				public UserPredicate getQuery() {
					return query;
				}

				@Override
				public FunctionCallFactory getFunctionCallFactory() {
					return pc.functionCallFactory();
				}

				@Override
				public Set<ConstructorSymbol> getUninterpretedFunctionSymbols() {
					return Collections.unmodifiableSet(uninterpFuncSymbols);
				}

				@Override
				public Set<TypeSymbol> getTypeSymbols() {
					return pc.symbolManager().getTypeSymbols();
				}

			};
		}
		
	}

}
