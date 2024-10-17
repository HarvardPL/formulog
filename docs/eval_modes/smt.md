---
title: Solver Modes and Incremental SMT Solving
layout: page
parent: Evaluation Modes
nav_order: 2
---

# Solver Modes and Incremental SMT Solving

The Formulog runtime associates one external SMT solver process per Formulog
worker thread. Each SMT query is a list of conjuncts. If the SMT solver is
invoked via the `is_sat_opt` or `get_model_opt` function, this list is
explicitly given by the programmer; otherwise, if the solver is invoked via the
`is_sat` or `is_valid` function, the Formulog runtime breaks the supplied
proposition into conjuncts.

Formulog supports three strategies for interacting with external SMT solvers;
they can be set using the `--smt-solver-mode` option.  Consider two SMT queries
`x` and `y`, where `x` immediately precedes `y` and both are lists of conjuncts.

- `naive`: reset the solver between queries `x` and `y` (do not use incremental
SMT solving).
- `push-pop`: try to use incremental SMT solving via the `push` and `pop` SMT
commands. This can work well when query `y` extends query `x`; e.g., `y = c ::
x`, where `c` is an additional conjunct; this situation most commonly occurs
when using [eager evaluation]({{ site.baseurl }}{% link eval_modes/eager.md %}).
- `check-sat-assuming`: try to use incremental SMT solving via the
`check-sat-assuming` SMT command. This caches conjuncts in the SMT solver in a
way such that they can be enabled or disabled per SMT query, and works well if
there are shared conjuncts between queries `x` and `y`, but query `x` is not
simply an extension of query `y` (e.g., it omits a conjunct in query `y`).

For more info, see the ICLP'20 extended abstract [Datalog-Based Systems Can Use Incremental SMT Solving](https://aaronbembenek.github.io/papers/datalog-incr-smt-iclp2020.pdf)
by Aaron Bembenek, Michael Ballantyne, Michael Greenberg, and Nada Amin.