package edu.harvard.seas.pl.formulog.validating.ast;

import java.util.ArrayList;
import java.util.HashSet;

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

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import edu.harvard.seas.pl.formulog.ast.BasicRule;
import edu.harvard.seas.pl.formulog.ast.ComplexConjunct;
import edu.harvard.seas.pl.formulog.ast.ComplexConjuncts.ComplexConjunctExnVisitor;
import edu.harvard.seas.pl.formulog.ast.Constructor;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Terms;
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.symbols.RelationSymbol;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class SimplifiedRule<R extends RelationSymbol> implements Rule<R, SimpleConjunct<R>> {

	private final Predicate<R> head;
	private final List<SimpleConjunct<R>> body;

	public static <R extends RelationSymbol> SimplifiedRule<R> make(BasicRule<R> rule) throws InvalidProgramException {
		Simplifier<R> simplifier = new Simplifier<>();
		for (ComplexConjunct<R> atom : rule) {
			try {
				simplifier.add(atom);
			} catch (InvalidProgramException e) {
				throw new InvalidProgramException("Problem simplifying this rule:\n" + rule
						+ "\nCould not simplify this atom: " + atom + "\nReason:\n" + e.getMessage());
			}
		}
		UserPredicate<R> head = rule.getHead();
		Set<Var> boundVars = simplifier.getBoundVars();
		if (!boundVars.containsAll(head.varSet())) {
			throw new InvalidProgramException("Unbound variables in head of rule:\n" + rule);
		}
		Predicate<R> newHead = Predicate.make(head.getSymbol(), head.getArgs(), boundVars, head.isNegated());
		return new SimplifiedRule<>(newHead, simplifier.getConjuncts());
	}

	private SimplifiedRule(Predicate<R> head, List<SimpleConjunct<R>> body) {
		this.head = head;
		this.body = body;
	}

	@Override
	public Predicate<R> getHead() {
		return head;
	}

	@Override
	public int getBodySize() {
		return body.size();
	}

	@Override
	public SimpleConjunct<R> getBody(int idx) {
		return body.get(idx);
	}

	@Override
	public Iterator<SimpleConjunct<R>> iterator() {
		return body.iterator();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((head == null) ? 0 : head.hashCode());
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
		SimplifiedRule<?> other = (SimplifiedRule<?>) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (head == null) {
			if (other.head != null)
				return false;
		} else if (!head.equals(other.head))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "SimplifiedRule [head=" + head + ", body=" + body + "]";
	}

	private static class Simplifier<R extends RelationSymbol> {

		private final List<SimpleConjunct<R>> acc = new ArrayList<>();
		private final Set<Var> boundVars = new HashSet<>();

		public void add(ComplexConjunct<R> atom) throws InvalidProgramException {
			List<ComplexConjunct<R>> todo = new ArrayList<>();
			SimpleConjunct<R> c = atom
					.accept(new ComplexConjunctExnVisitor<R, Void, SimpleConjunct<R>, InvalidProgramException>() {

						@Override
						public SimpleConjunct<R> visit(UnificationPredicate<R> unificationPredicate, Void input)
								throws InvalidProgramException {
							Term lhs = unificationPredicate.getLhs();
							Term rhs = unificationPredicate.getRhs();
							boolean leftBound = boundVars.containsAll(Terms.varSet(lhs));
							boolean rightBound = boundVars.containsAll(Terms.varSet(rhs));
							if (unificationPredicate.isNegated() && !(leftBound && rightBound)) {
								throw new InvalidProgramException();
							}
							if (leftBound && rightBound) {
								return Check.make(lhs, rhs, unificationPredicate.isNegated());
							} else if (rightBound) {
								if (lhs instanceof Var) {
									return Assignment.make((Var) lhs, rhs);
								}
								if (!(lhs instanceof Constructor)) {
									throw new InvalidProgramException();
								}
								return makeDestructor(rhs, (Constructor) lhs, todo);
							} else if (leftBound) {
								if (rhs instanceof Var) {
									return Assignment.make((Var) rhs, lhs);
								}
								if (!(rhs instanceof Constructor)) {
									throw new InvalidProgramException();
								}
								return makeDestructor(lhs, (Constructor) rhs, todo);
							} else {
								if (!(lhs instanceof Constructor) || !(rhs instanceof Constructor)) {
									throw new InvalidProgramException();
								}
								Constructor c1 = (Constructor) lhs;
								Constructor c2 = (Constructor) rhs;
								if (!c1.getSymbol().equals(c2.getSymbol())) {
									throw new InvalidProgramException("Unsatisfiable unification conjunct");
								}
								Term[] args1 = c1.getArgs();
								Term[] args2 = c2.getArgs();
								for (int i = 0; i < args1.length; ++i) {
									todo.add(UnificationPredicate.make(args1[i], args2[i], false));
								}
								return null;
							}
						}

						private Destructor<R> makeDestructor(Term boundTerm, Constructor unboundCtor,
								List<ComplexConjunct<R>> todo) {
							Term[] args = unboundCtor.getArgs();
							Var[] vars = new Var[args.length];
							for (int i = 0; i < args.length; ++i) {
								Var y = Var.getFresh(false);
								vars[i] = y;
								boundVars.add(y);
								todo.add(UnificationPredicate.make(y, args[i], false));
							}
							return Destructor.make(boundTerm, unboundCtor.getSymbol(), vars);
						}

						@Override
						public SimpleConjunct<R> visit(UserPredicate<R> userPredicate, Void input) {
							Term[] args = userPredicate.getArgs();
							Term[] newArgs = new Term[args.length];
							Set<Var> seen = new HashSet<>();
							for (int i = 0; i < args.length; ++i) {
								Term arg = args[i];
								if (boundVars.containsAll(Terms.varSet(arg))) {
									newArgs[i] = arg;
								} else if (arg instanceof Var && seen.add((Var) arg)) {
									newArgs[i] = arg;
								} else {
									Var y = Var.getFresh(false);
									newArgs[i] = y;
									todo.add(UnificationPredicate.make(y, arg, false));
								}
							}
							SimpleConjunct<R> c = Predicate.make(userPredicate.getSymbol(), newArgs, boundVars,
									userPredicate.isNegated());
							boundVars.addAll(seen);
							return c;
						}

					}, null);
			if (c != null) {
				acc.add(c);
			}
			for (ComplexConjunct<R> x : todo) {
				add(x);
			}
		}

		public List<SimpleConjunct<R>> getConjuncts() {
			return acc;
		}

		public Set<Var> getBoundVars() {
			return boundVars;
		}

	}

}
