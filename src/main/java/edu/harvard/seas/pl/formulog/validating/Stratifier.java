package edu.harvard.seas.pl.formulog.validating;

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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.jgrapht.Graph;
import org.jgrapht.alg.KosarajuStrongConnectivityInspector;
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.traverse.TopologicalOrderIterator;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Program;
import edu.harvard.seas.pl.formulog.ast.RelationProperties;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Exprs.ExprVisitor;
import edu.harvard.seas.pl.formulog.ast.FunctionCallFactory.FunctionCall;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.functions.CustomFunctionDef;
import edu.harvard.seas.pl.formulog.ast.functions.FunctionDef;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.symbols.PredicateFunctionSymbolFactory.PredicateFunctionSymbol;

public class Stratifier {

	private final Program prog;

	public Stratifier(Program prog) {
		this.prog = prog;
	}

	public List<Stratum> stratify() throws InvalidProgramException {
		Graph<Symbol, DependencyTypeWrapper> g = new DefaultDirectedGraph<>(DependencyTypeWrapper.class);
		for (Symbol sym : prog.getRuleSymbols()) {
			for (Rule r : prog.getRules(sym)) {
				DependencyFinder depends = new DependencyFinder();
				for (Atom bd : r.getBody()) {
					depends.processAtom(bd);
				}
				Atom hd = r.getHead();
				Symbol hdSym = hd.getSymbol();
				g.addVertex(hdSym);
				for (Symbol bdSym : depends) {
					g.addVertex(bdSym);
					g.addEdge(bdSym, hdSym, new DependencyTypeWrapper(depends.getDependencyType(bdSym)));
				}
			}
		}
		StrongConnectivityAlgorithm<Symbol, DependencyTypeWrapper> k = new KosarajuStrongConnectivityInspector<>(g);
		Graph<Graph<Symbol, DependencyTypeWrapper>, DefaultEdge> condensation = k.getCondensation();
		TopologicalOrderIterator<Graph<Symbol, DependencyTypeWrapper>, DefaultEdge> topo = new TopologicalOrderIterator<>(
				condensation);
		List<Stratum> strata = new ArrayList<>();
		while (topo.hasNext()) {
			boolean hasRecursiveNegationOrAggregation = false;
			Graph<Symbol, DependencyTypeWrapper> component = topo.next();
			for (DependencyTypeWrapper dw : component.edgeSet()) {
				DependencyType d = dw.get();
				if (d.equals(DependencyType.NEG_OR_AGG_IN_FUN)) {
					throw new InvalidProgramException("Not stratified...");
				}
				hasRecursiveNegationOrAggregation |= d.equals(DependencyType.NEG_OR_AGG_IN_REL);
			}
			strata.add(new Stratum(component.vertexSet(), hasRecursiveNegationOrAggregation));
		}
		return strata;
	}

	private class DependencyFinder implements Iterable<Symbol> {

		private final Set<Symbol> visitedFunctions = new HashSet<>();
		private final Set<Symbol> allDependencies = new HashSet<>();
		private final Set<Symbol> negOrAggFunDependencies = new HashSet<>();
		private final Set<Symbol> negOrAggRelDependencies = new HashSet<>();

		private boolean isAggregate(Atom a) {
			Symbol sym = a.getSymbol();
			RelationProperties props = prog.getRelationProperties(sym);
			return props != null && props.isAggregated();
		}

		public void processAtom(Atom a) {
			if (a.isNegated() || isAggregate(a)) {
				addNegOrAggRel(a.getSymbol());
			} else {
				addPositive(a.getSymbol());
			}
			for (Term t : a.getArgs()) {
				processTerm(t);
			}
		}

		public DependencyType getDependencyType(Symbol sym) {
			// Order is important here, since having a negative or aggregate
			// dependency within a function body subsumes having one in a
			// relation definition.
			if (negOrAggFunDependencies.contains(sym)) {
				return DependencyType.NEG_OR_AGG_IN_FUN;
			}
			if (negOrAggRelDependencies.contains(sym)) {
				return DependencyType.NEG_OR_AGG_IN_REL;
			}
			return DependencyType.POSITIVE;
		}

		private void addNegOrAggFun(Symbol sym) {
			negOrAggFunDependencies.add(sym);
			allDependencies.add(sym);
		}

		private void addNegOrAggRel(Symbol sym) {
			negOrAggRelDependencies.add(sym);
			allDependencies.add(sym);
		}

		private void addPositive(Symbol sym) {
			allDependencies.add(sym);
		}

		private void processTerm(Term t) {
			t.visit(new TermVisitor<Void, Void>() {

				@Override
				public Void visit(Var t, Void in) {
					return null;
				}

				@Override
				public Void visit(Constructor t, Void in) {
					for (Term arg : t.getArgs()) {
						arg.visit(this, null);
					}
					return null;
				}

				@Override
				public Void visit(Primitive<?> prim, Void in) {
					return null;
				}

				@Override
				public Void visit(Expr expr, Void in) {
					processExpr(expr);
					return null;
				}

			}, null);
		}

		private void processExpr(Expr expr) {
			expr.visit(new ExprVisitor<Void, Void>() {

				@Override
				public Void visit(MatchExpr matchExpr, Void in) {
					processTerm(matchExpr.getMatchee());
					for (MatchClause cl : matchExpr.getClauses()) {
						processTerm(cl.getLhs());
						processTerm(cl.getRhs());
					}
					return null;
				}

				@Override
				public Void visit(FunctionCall funcCall, Void in) {
					processFunctionSymbol(funcCall.getSymbol());
					for (Term arg : funcCall.getArgs()) {
						processTerm(arg);
					}
					return null;
				}

			}, null);
		}

		private void processFunctionSymbol(Symbol s) {
			assert prog.getFunctionSymbols().contains(s);
			if (!visitedFunctions.add(s)) {
				return;
			}
			if (s instanceof PredicateFunctionSymbol) {
				addNegOrAggFun(((PredicateFunctionSymbol) s).getPredicateSymbol());
				return;
			}
			FunctionDef def1 = prog.getDef(s);
			if (def1 instanceof CustomFunctionDef) {
				CustomFunctionDef def = (CustomFunctionDef) def1;
				processTerm(def.getBody());
			}
		}

		@Override
		public Iterator<Symbol> iterator() {
			return allDependencies.iterator();
		}

	}

	private static enum DependencyType {

		NEG_OR_AGG_IN_FUN,

		NEG_OR_AGG_IN_REL,

		POSITIVE;

	}

	// Needed because edges need to have unique objects as labels...
	private static class DependencyTypeWrapper {

		private final DependencyType d;

		public DependencyTypeWrapper(DependencyType d) {
			this.d = d;
		}

		public DependencyType get() {
			return d;
		}

	}

}
