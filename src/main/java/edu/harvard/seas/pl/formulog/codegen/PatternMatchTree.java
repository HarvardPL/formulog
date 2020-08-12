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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Expr;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.util.Pair;

/**
 * The class turns an ML-style pattern match expression into a tree that encodes
 * the same logic. <br>
 * <br>
 * Edges in the tree represent pattern matching logic: binding variables,
 * checking whether two constants are equal, and checking whether two
 * constructor symbols match up. <br>
 * <br>
 * The leafs of the tree are the right-hand side of the (pattern => expression)
 * pairs in the match expression; the path leading to a leaf corresponds to the
 * logic that must completed successfully for the corresponding pattern to be
 * matched. <br>
 * <br>
 * Non-leaf nodes contain the symbolic term that is being checked at that point
 * in the pattern-matching logic; e.g., the second argument of the scrutinee
 * term for the entire match expression. The children of a node are ordered,
 * with earlier children representing higher priority patterns (which is
 * necessary since patterns do not have to be mutually exclusive). <br>
 * <br>
 * Given a concrete scrutinee, a pattern match is simulated by walking the tree
 * (in its order of iteration). If you are at a leaf node, then it means the
 * pattern corresponding to the path to that leaf is matched, and you should
 * evaluate the expression associated with that leaf. If you are at an internal
 * node, then you instantiate the symbolic term at that node with the concrete
 * scrutinee and try to match it against each edge in order. You then travel
 * along the first edge that matches, backtracking if necessary.
 */
public class PatternMatchTree {

	private final Map<Node, List<Pair<Edge<?>, Node>>> m = new HashMap<>();
	private final Node root;

	/**
	 * Construct a pattern match tree from a list of (pattern => expression) pairs
	 * 
	 * @param clauses
	 *            The (pattern => expression) pairs
	 */
	public PatternMatchTree(List<Pair<Term, Term>> clauses) {
		PatternMatchingComputation k = PatternMatchingComputation.mk(clauses);
		root = build(k);
	}

	/**
	 * Return the root of the tree.
	 * 
	 * @return The root
	 */
	public Node getRoot() {
		return root;
	}

	/**
	 * Get a map from representing the outgoing edges of the given node. The map's
	 * iterator order matches the priority of the edges (high to low).
	 * 
	 * @param node
	 *            The node
	 * @return Map with the outgoing edges
	 */
	public Iterable<Pair<Edge<?>, Node>> getOutgoingEdges(Node node) {
		return m.get(node);
	}

	@Override
	public String toString() {
		String s = "{\n\troot=" + root + "\n";
		for (Map.Entry<Node, ?> e : m.entrySet()) {
			s += "\t" + e.getKey() + " -> " + e.getValue() + "\n";
		}
		return s + "}\n";
	}

	/**
	 * Turn a pattern-matching computation into a tree representing that
	 * computation.
	 * 
	 * @param k
	 *            The computation
	 * @return return The node at the root of that tree
	 */
	private Node build(PatternMatchingComputation k) {
		if (k.isFinished()) {
			return new Leaf(k.getFinalTerm());
		}
		Node node = new InternalNode(k.getCurrentSymbolicTerm());
		List<Pair<Edge<?>, Node>> outgoing = new ArrayList<>();
		for (Pair<Edge<?>, PatternMatchingComputation> p : k.stepComputation()) {
			outgoing.add(new Pair<>(p.fst(), build(p.snd())));
		}
		m.put(node, outgoing);
		return node;
	}

	/**
	 * This interface represents a term that is being matched upon; it is symbolic,
	 * in that at compile time we might not know its actual concrete value.
	 */
	public static interface SymbolicTerm {

	}

	/**
	 * This class represents the scrutinee of the match expression.
	 */
	public static enum BaseSymbolicTerm implements SymbolicTerm {

		INSTANCE;

		@Override
		public String toString() {
			return "B";
		}

	}

	/**
	 * The class represents a symbolic term resulting from indexing into the
	 * arguments of another symbolic term.
	 */
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

		@Override
		public String toString() {
			return base + "[" + index + "]";
		}

	}

	/**
	 * This class represents a pattern-matching computation; i.e., the logic that
	 * happens when you try to match a scrutinee against a sequence of (pattern =>
	 * expression) pairs.
	 */
	private static class PatternMatchingComputation {

		/**
		 * This field keeps track of all the symbolic terms that we are trying to match
		 * against patterns.
		 */
		private final Deque<SymbolicTerm> schema;
		/**
		 * This is an iterable representing all the computation that remains to be done.
		 * It consists of pairs. The first element of the pair is a deque of pattern
		 * terms; this deque should be the same size as the {@link #schema schema}
		 * field, and symbolic terms are pairwise matched against terms in this deque.
		 * The second element of the pair is the computation that happens if a complete
		 * pattern is matched (i.e., it is the right-hand side of a (pattern =>
		 * expression) pair).
		 */
		private final Iterable<Pair<Deque<Term>, Term>> continuation;

		private PatternMatchingComputation(Deque<SymbolicTerm> schema, Iterable<Pair<Deque<Term>, Term>> continuation) {
			this.schema = schema;
			this.continuation = continuation;
		}

		/**
		 * Construct a pattern-matching computation from a list of (pattern =>
		 * expression) pairs.
		 * 
		 * @param clauses
		 *            The (pattern => expression) pairs
		 * @return the pattern-matching computation
		 */
		public static PatternMatchingComputation mk(List<Pair<Term, Term>> clauses) {
			/*
			 * Initially, the schema is just the symbolic term representing the entire
			 * scrutinee, and the continuation represents the ordered (pattern =>
			 * expression) pairs.
			 */
			Deque<SymbolicTerm> schema = new ArrayDeque<>();
			schema.add(BaseSymbolicTerm.INSTANCE);
			List<Pair<Deque<Term>, Term>> continuation = new ArrayList<>();
			for (Pair<Term, Term> clause : clauses) {
				ArrayDeque<Term> k = new ArrayDeque<>();
				k.add(clause.fst());
				continuation.add(new Pair<>(k, clause.snd()));
			}
			return new PatternMatchingComputation(schema, continuation);
		}

		/**
		 * Return the pattern-matching logic that follows the current logic.
		 * 
		 * @return An iterable of pairs of edges and pattern-matching computations. The
		 *         pairs are in order of priority (high to low); the pattern-matching
		 *         computation for an edge represents the computation that follows the
		 *         logic represented by that edge.
		 */
		public Iterable<Pair<Edge<?>, PatternMatchingComputation>> stepComputation() {
			assert !isFinished();
			/* First, create new edges corresponding to the next step of the computation. */
			List<Pair<Edge<?>, Set<Pair<Deque<Term>, Term>>>> l = new ArrayList<>();
			Edge<?> lastEdge = null;
			Set<Pair<Deque<Term>, Term>> lastSet = null;
			for (Pair<Deque<Term>, Term> p : continuation) {
				Deque<Term> d = new ArrayDeque<>(p.fst());
				Edge<?> edge = step(d);
				p = new Pair<>(d, p.snd());
				if (edge.equals(lastEdge)) {
					lastSet.add(p);
				} else {
					lastEdge = edge;
					lastSet = new LinkedHashSet<>();
					lastSet.add(p);
					l.add(new Pair<>(lastEdge, lastSet));
				}
			}
			/*
			 * Second, create new pattern-matching computations representing the rest of the
			 * work to do along each edge.
			 */
			List<Pair<Edge<?>, PatternMatchingComputation>> l2 = new ArrayList<>();
			for (Pair<Edge<?>, Set<Pair<Deque<Term>, Term>>> p : l) {
				Edge<?> edge = p.fst();
				Deque<SymbolicTerm> newSchema = new ArrayDeque<>(schema);
				SymbolicTerm base = newSchema.removeFirst();
				if (edge instanceof CtorEdge) {
					/*
					 * If we're matching against a constructor symbol, we need to also match the
					 * arguments of the current scrutinee against its arguments.
					 */
					ConstructorSymbol sym = ((CtorEdge) edge).getLabel();
					for (int i = sym.getArity() - 1; i >= 0; --i) {
						newSchema.addFirst(new DerivedSymbolicTerm(base, i));
					}
				}
				PatternMatchingComputation k = new PatternMatchingComputation(newSchema, p.snd());
				l2.add(new Pair<>(edge, k));
			}
//			System.out.println(l2);
//			try {
//				System.in.read();
//			} catch (IOException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
			return l2;
		}

		/**
		 * Create an edge corresponding to the pattern matching logic for the first step
		 * in processing a deque of patterns. The provided deque is also updated.
		 * 
		 * @param d
		 *            The deque of patterns
		 * @return The edge
		 */
		private static Edge<?> step(Deque<Term> d) {
			Term next = d.removeFirst();
			Edge<?> edge = next.accept(tv, null);
			if (next instanceof Constructor) {
				/*
				 * If we are matching against a constructor, then we need to recursively match
				 * against its arguments
				 */
				Constructor ctor = (Constructor) next;
				Term[] args = ctor.getArgs();
				for (int i = args.length - 1; i >= 0; --i) {
					d.addFirst(args[i]);
				}
			}
			return edge;
		}

		/**
		 * Get the symbolic term that we are currently trying to match against a
		 * pattern.
		 * 
		 * @return The symbolic term
		 */
		public SymbolicTerm getCurrentSymbolicTerm() {
			assert !isFinished();
			return schema.getFirst();
		}

		/**
		 * Return true iff there are no more computational steps to take.
		 * 
		 * @return True iff there are no more computational steps to take
		 */
		public boolean isFinished() {
			return schema.isEmpty();
		}

		/**
		 * Return the expression to evaluate if the current pattern succeeds.
		 * 
		 * @return The expression
		 */
		public Term getFinalTerm() {
			assert isFinished();
			return continuation.iterator().next().snd();
		}

		@Override
		public String toString() {
			return "PatternMatchingComputation [schema=" + schema + ", continuation=" + continuation + "]";
		}

	}

	/**
	 * This field is used to turn a term into an edge corresponding to the first
	 * step of logic necessary for matching against that term.
	 */
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
			// Expressions cannot occur in patterns
			throw new AssertionError("impossible");
		}

	};

	/**
	 * This interface represents a node in the pattern match tree.
	 */
	public static interface Node {

		<I, O> O accept(NodeVisitor<I, O> visitor, I in);

	}

	public static interface NodeVisitor<I, O> {

		O visit(InternalNode node, I in);

		O visit(Leaf node, I in);

	}

	/**
	 * The class represents an internal (i.e., non-leaf) node in the tree.
	 */
	public static class InternalNode implements Node {

		private static AtomicInteger cnt = new AtomicInteger();
		
		private final SymbolicTerm symbolicTerm;
		private final int id = cnt.getAndIncrement();

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
			return "Node#" + id + "(" + symbolicTerm + ")";
		}

	}

	/**
	 * The class represents a leaf of the tree; it holds the computation on the
	 * right-hand side of a (pattern => expression) pair.
	 */
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
			return "Leaf(" + term + ")";
		}

	}

	/**
	 * This interface represents an edge in the tree. Edges correspond to pattern
	 * matching logic (i.e., binding a variable, or checking a constant or
	 * constructor), and this interface is parametric in the type of computation
	 * that needs to be performed.
	 *
	 * @param <T>
	 *            The type of the edge
	 */
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

	/**
	 * This edge represents pattern matching logic in which a variable is bound.
	 */
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
			return "VarEdge(" + label + ")";
		}

	}

	/**
	 * This edge represents pattern matching logic in which a primitive constant is
	 * checked.
	 */
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
			return "PrimEdge(" + label + ")";
		}

	}

	/**
	 * This edge represents pattern matching logic in which a constructor symbol is
	 * checked.
	 */
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
			return "CtorEdge(" + label + ")";
		}

	}

}
