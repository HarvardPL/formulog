package edu.harvard.seas.pl.formulog.unification;

import java.util.HashSet;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.Atoms;
import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;
import edu.harvard.seas.pl.formulog.ast.Atoms.AtomVisitorExn;
import edu.harvard.seas.pl.formulog.ast.Atoms.NormalAtom;
import edu.harvard.seas.pl.formulog.ast.Atoms.UnifyAtom;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Primitive;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.Terms.TermVisitor;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.ast.functions.Expr;
import edu.harvard.seas.pl.formulog.eval.EvaluationException;
import edu.harvard.seas.pl.formulog.symbols.Symbol;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public final class Unification {

	private Unification() {
		throw new AssertionError();
	}

	public static boolean canBindVars(Atom atom, Set<Var> boundVars) throws InvalidProgramException {
		if (atom.isNegated()) {
			return boundVars.containsAll(Atoms.varSet(atom));
		}
		return atom.visit(new AtomVisitorExn<Void, Boolean, InvalidProgramException>() {

			@Override
			public Boolean visit(NormalAtom normalAtom, Void in) throws InvalidProgramException {
				return handleNormalAtom(normalAtom, boundVars);
			}

			@Override
			public Boolean visit(UnifyAtom unifyAtom, Void in) throws InvalidProgramException {
				return handleUnifyAtom(unifyAtom, boundVars);
			}

		}, null);
	}

	private static boolean handleNormalAtom(NormalAtom atom, Set<Var> boundVars) {
		assert !atom.isNegated();
		Set<Var> nonFuncVars = new HashSet<>();
		Set<Var> funcVars = new HashSet<>();
		for (Term t : atom.getArgs()) {
			nonFuncVars.addAll(Terms.getBindingVarInstances(t));
			funcVars.addAll(Terms.getNonBindingVarInstances(t));
		}
		for (Var v : funcVars) {
			if (!boundVars.contains(v) && !nonFuncVars.contains(v)) {
				return false;
			}
		}
		return true;
	}

	private static boolean handleUnifyAtom(UnifyAtom atom, Set<Var> boundVars) throws InvalidProgramException {
		Term t1 = atom.getArgs()[0];
		Term t2 = atom.getArgs()[1];
		Set<Var> maybeBoundVars = new HashSet<>(boundVars);
		while (handleUnifyAtomHelper(t1, t2, maybeBoundVars)) {

		}
		return maybeBoundVars.containsAll(Atoms.varSet(atom));
	}

	private static boolean handleUnifyAtomHelper(Term t1, Term t2, Set<Var> boundVars) throws InvalidProgramException {
		boolean changed = false;
		if (Terms.isGround(t1, boundVars)) {
			changed |= boundVars.addAll(Terms.getBindingVarInstances(t2));
		}
		if (Terms.isGround(t2, boundVars)) {
			changed |= boundVars.addAll(Terms.getBindingVarInstances(t1));
		}
		if (t1 instanceof Constructor && t2 instanceof Constructor) {
			Constructor c1 = (Constructor) t1;
			Constructor c2 = (Constructor) t2;
			Symbol sym1 = c1.getSymbol();
			Symbol sym2 = c2.getSymbol();
			if (!sym1.equals(sym2)) {
				throw new InvalidProgramException(
						"Cannot unify a constructor of symbol " + sym1 + " with a constructor of symbol " + sym2);
			}
			Term[] args1 = c1.getArgs();
			Term[] args2 = c2.getArgs();
			assert args1.length == args2.length;
			boolean changed2;
			do {
				changed2 = false;
				for (int i = 0; i < args1.length; ++i) {
					changed2 |= handleUnifyAtomHelper(args1[i], args2[i], boundVars);
					changed |= changed2;
				}
			} while (changed2);
		}
		return changed;
	}

	public static boolean unify(Atom a1, Atom a2, Substitution s) throws EvaluationException {
		if (!a1.getSymbol().equals(a2.getSymbol())) {
			return false;
		}
		Term[] args1 = a1.getArgs();
		Term[] args2 = a2.getArgs();
		for (int i = 0; i < args1.length; ++i) {
			if (!unify(args1[i], args2[i], s)) {
				return false;
			}
		}
		return true;
	}

	public static void unsafeUnifyWithFact(NormalAtom atom, NormalAtom fact, Substitution s) {
		Term[] args1 = atom.getArgs();
		Term[] args2 = fact.getArgs();
		for (int i = 0; i < args1.length; ++i) {
			assert args2[i].isGround();
			unsafeUnify(args1[i], args2[i], s);
		}
	}

	private static void unsafeUnify(Term t1, Term t2, Substitution s) {
		t1.visit(new TermVisitor<Term, Void>() {

			@Override
			public Void visit(Var t, Term in) {
				s.put(t, in);
				return null;
			}

			@Override
			public Void visit(Constructor t, Term in) {
				Term[] args1 = t.getArgs();
				Term[] args2 = ((Constructor) in).getArgs();
				for (int i = 0; i < args1.length; ++i) {
					args1[i].visit(this, args2[i]);
				}
				return null;
			}

			@Override
			public Void visit(Primitive<?> prim, Term in) {
				return null;
			}

			@Override
			public Void visit(Expr expr, Term in) {
				return null;
			}

		}, t2);
	}

	public static boolean unify(Term t1, Term t2, Substitution s) throws EvaluationException {
		return unify2(t1, t2, s);
	}

	/*
	 * This assumes that the two terms are in a restricted form...
	 */
	public static boolean unify2(Term t1, Term t2, Substitution s) throws EvaluationException {
		t1 = Terms.lookup(t1, s);
		t2 = Terms.lookup(t2, s);

		if (t1 instanceof Var) {
			assert !(t2 instanceof Var);
			s.put((Var) t1, t2.normalize(s));
			return true;
		}
		if (t2 instanceof Var) {
			s.put((Var) t2, t1.normalize(s));
			return true;
		}

		if (t1 instanceof Expr) {
			t1 = t1.normalize(s);
		}
		if (t2 instanceof Expr) {
			t2 = t2.normalize(s);
		}

		if (t1 instanceof Primitive) {
			return t1.equals(t2);
		}
		assert !(t2 instanceof Primitive);

		Constructor c1 = (Constructor) t1;
		Constructor c2 = (Constructor) t2;

		if (!c1.getSymbol().equals(c2.getSymbol())) {
			return false;
		}

		Term[] args1 = c1.getArgs();
		Term[] args2 = c2.getArgs();
		for (int i = 0; i < args1.length; ++i) {
			if (!unify2(args1[i], args2[i], s)) {
				return false;
			}
		}

		return true;
	}

	/*
	 * This is a more sophisticated unification method than unify2 (i.e., it can
	 * unify terms that unify2 cannot), but it is too slow...
	 */
//	@SuppressWarnings("unused")
//	private static boolean unify1(Term t1, Term t2, Substitution s) throws EvaluationException {
//		// Handle some simple cases.
//		if (t1 instanceof Var && !s.containsKey((Var) t1)) {
//			t2 = t2.reduce(s);
//			s.put((Var) t1, t2.applySubstitution(s));
//			return true;
//		}
//		if (t2 instanceof Var && !s.containsKey((Var) t2)) {
//			t1 = t1.reduce(s);
//			s.put((Var) t2, t1.applySubstitution(s));
//			return true;
//		}
//
//		return (new Unifier(t1, t2, s)).unify();
//	}
//
//	private static class Unifier {
//
//		private final Term t1;
//		private final Term t2;
//		private final Substitution s;
//		private final Graph<Node, DefaultEdge> ugraph = new DefaultDirectedGraph<>(DefaultEdge.class);
//		// Invariant: a term is in dgraph iff it is not ground.
//		private final Graph<Node, DefaultEdge> dgraph = new SimpleGraph<>(DefaultEdge.class);
//		private final Map<Term, Node> memo = new HashMap<>();
//		private final Set<Node> ground = new HashSet<>();
//
//		public Unifier(Term t1, Term t2, Substitution s) {
//			this.t1 = t1;
//			this.t2 = t2;
//			this.s = s;
//		}
//
//		/*
//		 * Unification routines
//		 */
//
//		public boolean unify() throws EvaluationException {
//			if (!processPair(t1, t2)) {
//				return false;
//			}
//			Set<Node> lastFrontier = new HashSet<>(ground);
//			while (!lastFrontier.isEmpty()) {
//				Set<Node> frontier = new HashSet<>();
//				for (Node g : lastFrontier) {
//					assert !dgraph.containsVertex(g);
//					// ugraph might not contain vertex if it is coalesced in a previous iteration.
//					if (ugraph.containsVertex(g)) {
//						for (Node n : ugraphNeighbors(g)) {
//							if (!tryToCoalesce(g, n, frontier)) {
//								return false;
//							}
//						}
//						if (ugraph.degreeOf(g) == 0) {
//							ugraph.removeVertex(g);
//						}
//					}
//				}
//
//				Queue<Node> q = new ArrayDeque<>(frontier);
//				while (!q.isEmpty()) {
//					Node n = q.remove();
//					Term t = n.getTerm();
//					if (t instanceof FunctionCall) {
//						FunctionCall f = (FunctionCall) t;
//						Term r = f.evaluate(s);
//						n.setTerm(r);
//					}
//
//					if (dgraph.containsVertex(n)) {
//						for (Node dst : dgraphNeighbors(n)) {
//							if (dgraph.inDegreeOf(dst) == 1 && !frontier.contains(dst)) {
//								frontier.add(dst);
//								q.add(dst);
//								dst.setTerm(dst.getTerm().applySubstitution(s));
//							}
//						}
//						dgraph.removeVertex(n);
//					}
//				}
//
//				ground.addAll(frontier);
//				lastFrontier = frontier;
//			}
//
//			assert ugraph.vertexSet().isEmpty();
//			assert dgraph.vertexSet().isEmpty();
//			return true;
//		}
//
//		private boolean tryToCoalesce(Node src, Node dst, Set<Node> frontier) {
//			Term dstT = dst.getTerm();
//			if (dstT instanceof Var) {
//				assert !s.containsKey((Var) dstT);
//				s.put((Var) dstT, src.getTerm());
//				coalesce(src, dst, frontier);
//				return true;
//			} else {
//				if (dstT instanceof FunctionCall) {
//					assert !ground.contains(dst);
//					return true;
//				}
//				if (unifyGroundTermWithOther(src.getTerm(), dst.getTerm(), frontier)) {
//					coalesce(src, dst, frontier);
//					return true;
//				} else {
//					return false;
//				}
//			}
//		}
//
//		private void coalesce(Node eater, Node eaten, Set<Node> frontier) {
//			ugraphRemoveEdge(eater, eaten);
//			if (ugraph.degreeOf(eaten) > 0) {
//				frontier.add(eater);
//			}
//			for (Node dst : ugraphNeighbors(eaten)) {
//				addEdge(eater, dst, ugraph);
//			}
//			ugraph.removeVertex(eaten);
//			frontier.add(eaten);
//			assert eater.getTerm().isGround();
//			eaten.setTerm(eater.getTerm());
//		}
//
//		private boolean unifyGroundTermWithOther(Term grndT, Term other, Set<Node> frontier) {
//			assert grndT.isGround();
//			assert grndT instanceof Constructor || grndT instanceof Primitive;
//			return other.visit(new TermVisitor<Term, Boolean>() {
//
//				@Override
//				public Boolean visit(Var t, Term in) {
//					if (s.containsKey(t)) {
//						if (!s.get(t).equals(in)) {
//							return false;
//						}
//						assert getNode(t).getTerm().equals(in);
//					} else {
//						s.put(t, in);
//						getNode(t).setTerm(in);
//					}
//					frontier.add(getNode(t));
//					return true;
//				}
//
//				@Override
//				public Boolean visit(Constructor t, Term in) {
//					if (!(in instanceof Constructor)) {
//						return false;
//					}
//					Constructor cin = (Constructor) in;
//					if (!cin.getSymbol().equals(t.getSymbol())) {
//						return false;
//					}
//					Term[] inargs = cin.getArgs();
//					Term[] targs = t.getArgs();
//					boolean ok = true;
//					for (int i = 0; i < targs.length; ++i) {
//						ok &= targs[i].visit(this, inargs[i]);
//					}
//					return ok;
//				}
//
//				@Override
//				public Boolean visit(Primitive<?> prim, Term in) {
//					return in.equals(prim);
//				}
//
//				@Override
//				public Boolean visit(Expr expr, Term in) {
//					throw new AssertionError();
//				}
//
//			}, grndT);
//		}
//
//		/*
//		 * Graph setup
//		 */
//
//		private boolean processPair(Term t1, Term t2) throws EvaluationException {
//			t1 = lookup(t1);
//			t2 = lookup(t2);
//			if (t1 instanceof Constructor && t2 instanceof Constructor) {
//				Constructor c1 = (Constructor) t1;
//				Constructor c2 = (Constructor) t2;
//				if (!c1.getSymbol().equals(c2.getSymbol())) {
//					return false;
//				}
//				Term[] args1 = c1.getArgs();
//				Term[] args2 = c2.getArgs();
//				boolean ok = true;
//				for (int i = 0; i < args1.length; ++i) {
//					ok &= processPair(args1[i], args2[i]);
//				}
//				return ok;
//			} else if (t1 instanceof Primitive && t2 instanceof Primitive) {
//				return t1.equals(t2);
//			} else {
//				Node node1 = flatten(t1);
//				Node node2 = flatten(t2);
//				addEdge(node1, node2, ugraph);
//				return true;
//			}
//		}
//
//		private Node flatten(Term t) throws EvaluationException {
//			t = lookup(t);
//			Node tnode = getNode(t);
//			t.visit(new TermVisitorExn<Void, Void, EvaluationException>() {
//
//				@Override
//				public Void visit(Var t, Void in) {
//					return null;
//				}
//
//				@Override
//				public Void visit(Constructor t, Void in) throws EvaluationException {
//					int arity = t.getSymbol().getArity();
//					if (arity == 0) {
//						ground.add(tnode);
//					} else {
//						dgraph.addVertex(tnode);
//						Term[] vars = new Var[arity];
//						Term[] args = t.getArgs();
//						for (int i = 0; i < arity; ++i) {
//							Node vnode = flattenHelper(args[i]);
//							vars[i] = vnode.getTerm();
//							addEdge(vnode, tnode, dgraph);
//						}
//						t = t.copyWithNewArgs(vars);
//						tnode.setTerm(t);
//					}
//					return null;
//				}
//
//				@Override
//				public Void visit(Primitive<?> prim, Void in) {
//					ground.add(tnode);
//					return null;
//				}
//
//				@Override
//				public Void visit(FunctionCall function, Void in) throws EvaluationException {
//					int arity = function.getSymbol().getArity();
//					// Corner case: zero-ary functions, which can be evaluated right away
//					if (arity == 0) {
//						Term tt = function.evaluate(EmptySubstitution.INSTANCE);
//						tnode.setTerm(tt);
//						// Every term returned by a function call must be ground
//						ground.add(tnode);
//					} else {
//						dgraph.addVertex(tnode);
//						Term[] vars = new Var[arity];
//						Term[] args = function.getArgs();
//						for (int i = 0; i < arity; ++i) {
//							Node vnode = flattenHelper(args[i]);
//							vars[i] = vnode.getTerm();
//							addEdge(vnode, tnode, dgraph);
//						}
//						tnode.setTerm(function.copyWithNewArgs(vars));
//					}
//					return null;
//				}
//
//			}, null);
//			return tnode;
//		}
//
//		private Node flattenHelper(Term t) throws EvaluationException {
//			t = lookup(t);
//			if (t instanceof Var) {
//				return getNode(t);
//			}
//			Var v = Var.getFresh();
//			Node vnode = getNode(v);
//			Node tnode = flatten(t);
//			addEdge(vnode, tnode, ugraph);
//			return vnode;
//		}
//
//		/*
//		 * Helpers
//		 */
//
//		private Iterable<Node> ugraphNeighbors(Node src) {
//			Set<Node> neighbors = new HashSet<>();
//			for (DefaultEdge e : ugraph.edgesOf(src)) {
//				Node dst = ugraph.getEdgeTarget(e);
//				if (dst == src) {
//					dst = ugraph.getEdgeSource(e);
//				}
//				neighbors.add(dst);
//			}
//			return neighbors;
//		}
//
//		private void ugraphRemoveEdge(Node src, Node dst) {
//			ugraph.removeAllEdges(src, dst);
//			ugraph.removeAllEdges(dst, src);
//		}
//
//		private Iterable<Node> dgraphNeighbors(Node src) {
//			return dgraph.outgoingEdgesOf(src).stream().map(e -> dgraph.getEdgeTarget(e)).collect(Collectors.toSet());
//		}
//
//		private void addEdge(Node v1, Node v2, Graph<Node, ?> graph) {
//			graph.addVertex(v1);
//			graph.addVertex(v2);
//			if (!v1.equals(v2) && !graph.containsEdge(v1, v2)) {
//				graph.addEdge(v1, v2);
//			}
//		}
//
//		private Node getNode(Term t) {
//			return Util.lookupOrCreate(memo, t, () -> new Node(t));
//		}
//
//		private Term lookup(Term t) {
//			if (t instanceof Var && s.containsKey((Var) t)) {
//				t = s.get((Var) t);
//			}
//			return t;
//		}
//
//	}
//
//	private static class Node {
//
//		private Term t;
//
//		public Node(Term t) {
//			this.t = t;
//		}
//
//		public Term getTerm() {
//			return t;
//		}
//
//		public void setTerm(Term t) {
//			this.t = t;
//		}
//
//		@Override
//		public String toString() {
//			return t.toString();
//		}
//
//	}

}
