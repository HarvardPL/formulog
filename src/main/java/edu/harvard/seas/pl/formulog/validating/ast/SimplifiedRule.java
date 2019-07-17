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
import edu.harvard.seas.pl.formulog.ast.UnificationPredicate;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.validating.InvalidProgramException;

public class SimplifiedRule implements Rule<SimplePredicate, SimpleConjunct> {

	private final SimplePredicate head;
	private final List<SimpleConjunct> body;

	public static SimplifiedRule make(BasicRule rule) throws InvalidProgramException {
		Simplifier simplifier = new Simplifier();
		for (ComplexConjunct atom : rule) {
			try {
				simplifier.add(atom);
			} catch (InvalidProgramException e) {
				throw new InvalidProgramException("Problem simplifying this rule:\n" + rule
						+ "\nCould not simplify this atom: " + atom + "\nReason:\n" + e.getMessage());
			}
		}
		UserPredicate head = rule.getHead();
		Set<Var> boundVars = simplifier.getBoundVars();
		if (!boundVars.containsAll(head.varSet())) {
			throw new InvalidProgramException("Unbound variables in head of rule:\n" + rule);
		}
		SimplePredicate newHead = SimplePredicate.make(head.getSymbol(), head.getArgs(), boundVars, head.isNegated());
		return new SimplifiedRule(newHead, simplifier.getConjuncts());
	}

	private SimplifiedRule(SimplePredicate head, List<SimpleConjunct> body) {
		this.head = head;
		this.body = body;
	}

	@Override
	public SimplePredicate getHead() {
		return head;
	}

	@Override
	public int getBodySize() {
		return body.size();
	}

	@Override
	public SimpleConjunct getBody(int idx) {
		return body.get(idx);
	}

	@Override
	public Iterator<SimpleConjunct> iterator() {
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
		SimplifiedRule other = (SimplifiedRule) obj;
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

	private static class Simplifier {

		private final List<SimpleConjunct> acc = new ArrayList<>();
		private final Set<Var> boundVars = new HashSet<>();

		public void add(ComplexConjunct atom) throws InvalidProgramException {
			List<ComplexConjunct> todo = new ArrayList<>();
			SimpleConjunct c = atom
					.accept(new ComplexConjunctExnVisitor<Void, SimpleConjunct, InvalidProgramException>() {

						@Override
						public SimpleConjunct visit(UnificationPredicate unificationPredicate, Void input)
								throws InvalidProgramException {
							Term lhs = unificationPredicate.getLhs();
							Term rhs = unificationPredicate.getRhs();
							boolean leftBound = boundVars.containsAll(lhs.varSet());
							boolean rightBound = boundVars.containsAll(rhs.varSet());
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

						private Destructor makeDestructor(Term boundTerm, Constructor unboundCtor,
								List<ComplexConjunct> todo) {
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
						public SimpleConjunct visit(UserPredicate userPredicate, Void input) {
							Term[] args = userPredicate.getArgs();
							Term[] newArgs = new Term[args.length];
							Set<Var> seen = new HashSet<>();
							for (int i = 0; i < args.length; ++i) {
								Term arg = args[i];
								if (boundVars.containsAll(arg.varSet())) {
									newArgs[i] = arg;
								} else if (arg instanceof Var && seen.add((Var) arg)) {
									newArgs[i] = arg;
								} else {
									Var y = Var.getFresh(false);
									newArgs[i] = y;
									todo.add(UnificationPredicate.make(y, arg, false));
								}
							}
							SimpleConjunct c = SimplePredicate.make(userPredicate.getSymbol(), newArgs, boundVars,
									userPredicate.isNegated());
							boundVars.addAll(seen);
							return c;
						}

					}, null);
			if (c != null) {
				acc.add(c);
			}
			for (ComplexConjunct x : todo) {
				add(x);
			}
		}

		public List<SimpleConjunct> getConjuncts() {
			return acc;
		}

		public Set<Var> getBoundVars() {
			return boundVars;
		}

	}

}
