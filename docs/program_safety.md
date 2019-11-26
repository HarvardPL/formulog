# Program safety

Formulog imposes some restrictions on programs so that it can give guarantees about runtime behavior. Beyond the type system, these restrictions fall into two categories: restrictions on variable usage and restrictions on negation.

## Variable usage

Formulog requires that every variable in a rule is "bound." A variable can be bound if it appears in a binding position, if it is an anonymous variable (see below) that occurs as a top-level argument to a negated atom, or if it is explicitly unified with a ground term or bound variable via the `=` built-in predicate (for example, `X` is bound via the atom `X = 42`). A position is binding if it is in the argument to a positive (i.e., non-negated) atom in the rule body without also being in the argument to a function call.

Let's consider some examples of each of these cases. Here are some rules that are allowed:
```
p :- X = Y, Y = 42.
p :- (X, 0) = (42, Y).
p :- !q(_).
p :- !s(42, _).
q(X) :- r(X).
q(X) :- r(X), !r(X).
q(X) :- s(f(X), X). (* where f is a function *)
```

And here are some rules that are not allowed:
```
p :- X = Y, Y = Z.
p :- (X, 0) = (Z, Y).
q(X) :- p.
q(X) :- !r(X).
q(X) :- r(f(X)). (* where f is a function *)
```

These restrictions ensure that every variable is bound to a ground term going into a function call and that rules derive only ground facts.

### Anonymous variables

To help catch bugs related to variable usage, Formulog requires that every variable that does not start with an underscore occurs more than once in its scope. Every variable that begins with an underscore is treated as "anonymous," in that every occurrence of that variable represents a distinct variable. For this reason, Formulog also does not allow any variable that begins with an underscore to occur more than once in a scope, except for the special (fully anonymous) variable `_`.

## Negation

To ensure that every program has a least model, Formulog requires the use of stratified negation, a common restriction in Datalog. Intuitively, stratified negation ensures that there are no recursive negative dependencies between predicates.

Since Formulog allows predicate symbols to appear in function bodies, determining whether a Formulog program is stratified is slightly more complicated than in the Datalog case. To determine if a program is stratified we construct a dependence graph, where each node represents a different predicate. There is a "positive" edge from a predicate `p` to a predicate `q` if `p` appears in a positive atom in the body of a rule defining `q`. There is a "negative" edge from `p` to `q` if `p` appears in a negated atom in the body of a rule defining `q`, or `p` appears in the body of a function that may be transitively invoked from a rule defining `q`. A program is stratified if there are no cycles in the dependence graph that include a "negative" edge.
