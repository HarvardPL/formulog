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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.TodoException;

public class PatternMatchingTree {

	private final Map<Node, List<Pair<Edge<?>, Node>>> m = new HashMap<>();
	private final Root root = new Root();
	
	public PatternMatchingTree(MatchExpr match) {
		throw new TodoException();
	}
	
	public Root getRoot() {
		return root; 
	}
	
	public Iterable<Pair<Edge<?>, Node>> getOutgoingEdges(Node node) {
		return m.get(node);
	}
	
	@Override
	public String toString() {
		return "PatternMatchingTree [m=" + m + ", root=" + root + "]";
	}

	public static interface Node {

		<I, O> O accept(NodeVisitor<I, O> visitor, I in);
		
	}
	
	public static interface NodeVisitor<I, O> {
	
		O visit(Root node, I in);
		
		O visit(InternalNode node, I in);
		
		O visit(Leaf node, I in);
		
	}
	
	public static class Root implements Node {

		@Override
		public <I, O> O accept(NodeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "Root []";
		}
		
	}
	
	public static class InternalNode implements Node {

		private final int termIndex;
		
		public InternalNode(int termIndex) {
			this.termIndex = termIndex;
		}
		
		public int getTermIndex() {
			return termIndex;
		}
		
		@Override
		public <I, O> O accept(NodeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "InternalNode [termIndex=" + termIndex + "]";
		}
		
	}
	
	public static class Leaf implements Node {

		private final Term term;
		
		public Leaf(Term term) {
			this.term = term;
		}
		
		public Term getTerm() {
			return term;
		}
		
		@Override
		public <I, O> O accept(NodeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "Leaf [term=" + term + "]";
		}
		
	}

	public static interface Edge<T> {

		T getLabel();
		
		<I, O> O accept(EdgeVisitor<I, O> visitor, I in);

	}
	
	public static interface EdgeVisitor<I, O> {
		
		O visit(VarEdge e, I in);
		
		O visit(PrimEdge e, I in);
		
		O visit(CtorEdge e, I in);
		
	}

	private static abstract class AbstractEdge<T> implements Edge<T> {
	
		protected final T label;
		
		public AbstractEdge(T label) {
			this.label = label;
		}

		@Override
		public T getLabel() {
			return label;
		}
		
	}
	
	public static class VarEdge extends AbstractEdge<Var> {

		public VarEdge(Var label) {
			super(label);
		}

		@Override
		public <I, O> O accept(EdgeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "VarEdge [label=" + label + "]";
		}

	}
	
	public static class PrimEdge extends AbstractEdge<Primitive<?>> {

		public PrimEdge(Primitive<?> label) {
			super(label);
		}

		@Override
		public <I, O> O accept(EdgeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "PrimEdge [label=" + label + "]";
		}
		
	}
	
	public static class CtorEdge extends AbstractEdge<ConstructorSymbol> {

		public CtorEdge(ConstructorSymbol label) {
			super(label);
		}

		@Override
		public <I, O> O accept(EdgeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "CtorEdge [label=" + label + "]";
		}
		
	}

}
