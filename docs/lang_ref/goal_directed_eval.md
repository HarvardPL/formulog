---
title: Goal-Directed Evaluation
layout: page
parent: Language Reference
nav_order: 3
---

# Goal-Directed Evaluation

By default, Formulog uses a standard bottom-up, saturating evaluation strategy.
However, you can also trigger a form of goal-directed, top-down execution if you
include a query in your Formulog program. A query is a rule with an empty head
and a single (non-negated) body atom; for example, `:- p(X, "a").` is a query.
Each program can only have a single query.

The Formulog runtime will use the query to rewrite your program using (a variant
of) the magic set transformation technique. The rewritten program simulates
top-down evaluation when it is evaluated bottom-up. The rewriting happens after
type checking, but before program validation (i.e., before the checks described
in the "Program safety" section are run). This means that you are allowed to
write "invalid" Formulog programs, so long as that when they are rewritten, they
pass the validation checks. For example, this program is invalid evaluated
bottom-up, since there are unbound variables (in the head of the rules):

```
rel member(i32, i32 list)
member(X, X :: _Xs).
member(X, _Y :: Xs) :- member(X, Xs).
```

However, when we add the query `:- member(_X, [1, 2, 3]).`, the program is
rewritten to a valid program that can be evaluated bottom-up:

```
input_member_fb(Xs) :- sup_0_0(_0, Xs).
input_member_fb([1, 2, 3]).
member(X, X :: Xs) :- input_member_fb(X :: Xs).
member(X, _0 :: Xs) :- sup_0_0(_0, Xs), member(X, Xs).
sup_0_0(_0, Xs) :- input_member_fb(_0 :: Xs).
```

Our magic set transformation technique guarantees that if the original program
meets the requirements of stratified negation, then the rewritten program will
also be stratified. However, the transformation can turn a program that
terminates into a program that does not terminate. Also, it cannot be used with
predicates that are "invoked" from the functional fragment of Formulog.

## Query Syntax

Queries are in the form `:- A.` where `A` is a positive (non-negated) atom. The
typical rules about variable usage apply (see the "Anonymous variables" section
of the [Program Safety page]({{ site.baseurl }}{% link lang_ref/program_safety.md %})). If you want to have a query consisting of
multiple atoms, write a rule defining a new relation and then query that
relation. For example, the hypothetical query `:- A, B.` could be rewritten as
the rule `R :- A, B.` and query `:- R.`. There can be only one query per
program.

## Partial Goal-Directed Evaluation

It is also possible to only use goal-directed evaluation for part of a program.
You can control this by annotating IDB relation declarations with
`@bottomup` and `@topdown`:

```
@bottomup
rel foo(i32, string)

@topdown
rel bar(i32, i32, string)
```

A relation annotated as `@bottomup` will always be evaluated bottom-up (i.e., in
an exhaustive fashion), and a relation annotated as `@topdown` will always be
evaluated top-down (i.e., in a goal-directed fashion). These annotations can be
used whether or not a top-level query is supplied, and there are no restrictions
on how bottom-up and top-down relations can interact with each other (outside of
the normal restriction of stratified negation). Furthermore, not every relation
needs to be annotated. An unannotated relation will be evaluated bottom-up in
the absence of a top-level query, and top-down otherwise.
