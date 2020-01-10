package edu.harvard.seas.pl.formulog.codegen;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;

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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.MatchClause;
import edu.harvard.seas.pl.formulog.ast.MatchExpr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;
import edu.harvard.seas.pl.formulog.util.Util;

public class PatternMatchingTree {

	private final Map<Node, Map<Edge<?>, Node>> m = new HashMap<>();
	private final Node root;

	public PatternMatchingTree(MatchExpr match) {
		Continuation k = Continuation.mk(match.getClauses());
		root = build(k);
	}

	public Node getRoot() {
		return root;
	}

	public Map<Edge<?>, Node> getOutgoingEdges(Node node) {
		return Collections.unmodifiableMap(m.get(node));
	}

	@Override
	public String toString() {
		return "PatternMatchingTree [m=" + m + ", root=" + root + "]";
	}

	private Node build(Continuation k) {
		if (k.isFinished()) {
			return new Leaf(k.getFinalTerm());
		}
		Node node = new InternalNode(k.getCurrentSymbolicTerm());
		Map<Edge<?>, Node> outgoing = new LinkedHashMap<>();
		for (Map.Entry<Edge<?>, Continuation> e : k.split().entrySet()) {
			outgoing.put(e.getKey(), build(e.getValue()));
		}
		m.put(node, outgoing);
		return node;
	}

	public static interface SymbolicTerm {

	}

	public static enum BaseSymbolicTerm implements SymbolicTerm {

		INSTANCE;

	}

	public static class DerivedSymbolicTerm implements SymbolicTerm {

		private final SymbolicTerm base;
		private final int index;

		private DerivedSymbolicTerm(SymbolicTerm base, int index) {
			this.base = base;
			this.index = index;
		}

		public SymbolicTerm getBase() {
			return base;
		}

		public int getIndex() {
			return index;
		}

	}

	private static class Continuation {

		private final Deque<SymbolicTerm> schema;
		private final Iterable<Pair<Deque<Term>, Term>> continuation;

		private Continuation(Deque<SymbolicTerm> schema, Iterable<Pair<Deque<Term>, Term>> continuation) {
			this.schema = schema;
			this.continuation = continuation;
		}

		public static Continuation mk(List<MatchClause> match) {
			Deque<SymbolicTerm> schema = new ArrayDeque<>();
			schema.add(BaseSymbolicTerm.INSTANCE);
			List<Pair<Deque<Term>, Term>> continuation = new ArrayList<>();
			for (MatchClause clause : match) {
				ArrayDeque<Term> k = new ArrayDeque<>();
				k.add(clause.getLhs());
				continuation.add(new Pair<>(k, clause.getRhs()));
			}
			return new Continuation(schema, continuation);
		}

		public Map<Edge<?>, Continuation> split() {
			assert !isFinished();
			Map<Edge<?>, Set<Pair<Deque<Term>, Term>>> m = new LinkedHashMap<>();
			for (Pair<Deque<Term>, Term> p : continuation) {
				Deque<Term> d = new ArrayDeque<>(p.fst());
				Edge<?> edge = step(d);
				p = new Pair<>(d, p.snd());
				Util.lookupOrCreate(m, edge, () -> new LinkedHashSet<>()).add(p);
			}
			Map<Edge<?>, Continuation> m2 = new LinkedHashMap<>();
			for (Edge<?> edge : m.keySet()) {
				Deque<SymbolicTerm> newSchema = new ArrayDeque<>(schema);
				SymbolicTerm base = newSchema.removeFirst();
				if (edge instanceof CtorEdge) {
					ConstructorSymbol sym = ((CtorEdge) edge).getLabel();
					for (int i = sym.getArity() - 1; i >= 0; --i) {
						newSchema.addFirst(new DerivedSymbolicTerm(base, i));
					}
				}
				Continuation k = new Continuation(newSchema, m.get(edge));
				m2.put(edge, k);
			}
			return m2;
		}

		private Edge<?> step(Deque<Term> d) {
			Term next = d.removeFirst();
			Edge<?> edge = next.accept(tv, null);
			if (next instanceof Constructor) {
				Constructor ctor = (Constructor) next;
				Term[] args = ctor.getArgs();
				for (int i = args.length - 1; i >= 0; --i) {
					d.addFirst(args[i]);
				}
			}
			return edge;
		}

		public SymbolicTerm getCurrentSymbolicTerm() {
			assert !isFinished();
			return schema.getFirst();
		}

		public boolean isFinished() {
			return schema.isEmpty();
		}

		public Term getFinalTerm() {
			assert isFinished();
			return continuation.iterator().next().snd();
		}

	}

	private static final TermVisitor<Void, Edge<?>> tv = new TermVisitor<Void, Edge<?>>() {

		@Override
		public Edge<?> visit(Var x, Void in) {
			return new VarEdge(x);
		}

		@Override
		public Edge<?> visit(Constructor c, Void in) {
			return new CtorEdge(c.getSymbol());
		}

		@Override
		public Edge<?> visit(Primitive<?> p, Void in) {
			return new PrimEdge(p);
		}

		@Override
		public Edge<?> visit(Expr e, Void in) {
			throw new AssertionError("impossible");
		}

	};

	public static interface Node {

		<I, O> O accept(NodeVisitor<I, O> visitor, I in);

	}

	public static interface NodeVisitor<I, O> {

		O visit(InternalNode node, I in);

		O visit(Leaf node, I in);

	}

	public static class InternalNode implements Node {

		private final SymbolicTerm symbolicTerm;

		public InternalNode(SymbolicTerm symbolicTerm) {
			this.symbolicTerm = symbolicTerm;
		}

		public SymbolicTerm getSymbolicTerm() {
			return symbolicTerm;
		}

		@Override
		public <I, O> O accept(NodeVisitor<I, O> visitor, I in) {
			return visitor.visit(this, in);
		}

		@Override
		public String toString() {
			return "InternalNode [symbolicTerm=" + symbolicTerm + "]";
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

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((label == null) ? 0 : label.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			@SuppressWarnings("rawtypes")
			AbstractEdge other = (AbstractEdge) obj;
			if (label == null) {
				if (other.label != null)
					return false;
			} else if (!label.equals(other.label))
				return false;
			return true;
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
