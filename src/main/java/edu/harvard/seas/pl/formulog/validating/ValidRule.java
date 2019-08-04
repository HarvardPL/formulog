package edu.harvard.seas.pl.formulog.validating;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;

import edu.harvard.seas.pl.formulog.ast.AbstractRule;
import edu.harvard.seas.pl.formulog.ast.ComplexLiteral;
import edu.harvard.seas.pl.formulog.ast.Rule;
import edu.harvard.seas.pl.formulog.ast.UserPredicate;
import edu.harvard.seas.pl.formulog.ast.Var;
import edu.harvard.seas.pl.formulog.unification.Unification;
import edu.harvard.seas.pl.formulog.util.Util;

public class ValidRule extends AbstractRule<UserPredicate, ComplexLiteral> {

	public static ValidRule make(Rule<UserPredicate, ComplexLiteral> rule, BiFunction<ComplexLiteral, Set<Var>, Integer> score)
			throws InvalidProgramException {
		try {
			List<ComplexLiteral> body = Util.iterableToList(rule);
			Set<Var> vars = new HashSet<>();
			order(body, score, vars);
			UserPredicate head = rule.getHead();
			if (!head.getSymbol().isIdbSymbol()) {
				throw new InvalidProgramException("Cannot create a rule for non-IDB symbol " + head.getSymbol());
			}
			if (!vars.containsAll(head.varSet())) {
				String msg = "There are unbound variables in the head of a rule:";
				for (Var x : head.varSet()) {
					if (!vars.contains(x)) {
						msg += " " + x;
					}
				}
				throw new InvalidProgramException(msg);
			}
			return new ValidRule(head, body);
		} catch (InvalidProgramException e) {
			throw new InvalidProgramException(e.getMessage() + "\n" + rule);
		}
	}

	public static void order(List<ComplexLiteral> atoms, BiFunction<ComplexLiteral, Set<Var>, Integer> score,
			Set<Var> boundVars) throws InvalidProgramException {
		List<ComplexLiteral> newList = new ArrayList<>();
		// Using a linked hash set ensures the sort is stable.
		Set<ComplexLiteral> unplaced = new LinkedHashSet<>(atoms);
		while (!unplaced.isEmpty()) {
			ComplexLiteral bestLit = null;
			int bestScore = -1;
			for (ComplexLiteral l : unplaced) {
				if (Unification.canBindVars(l, boundVars)) {
					int localScore = score.apply(l, boundVars);
					if (localScore > bestScore) {
						bestScore = localScore;
						bestLit = l;
					}
				}
			}
			if (bestLit == null) {
				throw new InvalidProgramException("Literals do not admit an evaluable reordering");
			}
			newList.add(bestLit);
			boundVars.addAll(bestLit.varSet());
			unplaced.remove(bestLit);
		}
		atoms.clear();
		atoms.addAll(newList);
	}

	private ValidRule(UserPredicate head, List<ComplexLiteral> body) {
		super(head, body);
	}

}
