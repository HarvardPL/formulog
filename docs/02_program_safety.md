# Program safety

Formulog imposes some restrictions on programs so that it can give guarantees
about runtime behavior. Beyond the type system, these restrictions fall into
two categories: restrictions on variable usage and restrictions on negation.

## Variable usage

Correct variable usage is a tricky aspect of logic programming; this section
describes Formulog's restrictions on this front.

### Anonymous variables

To help catch bugs related to variable usage, Formulog requires that every
variable that does not start with an underscore occurs more than once in its
scope. Every variable that begins with an underscore is treated as "anonymous,"
in that every occurrence of that variable represents a distinct variable. For
this reason, Formulog does not allow any variable that begins with an underscore
to occur more than once in a scope, except for the traditional anonymous
variable `_`.

### Binding variables

Formulog requires that every variable in a rule is "bound." In what follows, we
use the identifiers `p` for a relation, `c` for a constructor, and `f` for a
function. A variable is bound when:

* it is explicitly unified via the `=` built-in predicate with a term that does
  not contain any unbound variables (e.g., `X` and `Y` are bound via the atom
  `(X, 0) = (42, Y)`);
* it is an anonymous variable that occurs as a top-level argument to a negated
  atom (e.g., `_X` is considered bound in `!p(_X)`); or
* it occurs in the argument to a positive atom, and that occurrence is not also
  the argument to a function call. For example, the occurrence of `X` in the
  atom `p(c(X))` is bound, but it is not bound in the atom `p(f(X))`.
  
Furthemore, the ML fragment of Formulog is evaluated using call-by-value
semantics, which means that the arguments to a function need to be normalized
and ground (i.e., variable-free) before a call site can be evaluated.
Consequently, every variable occurring as an argument to a function must be
bound going into the call site.

To check whether these variable binding conditions are met, the Formulog runtime
currently performs a single pass over the rule, going from left to right across
the rule body, and then finishing on the rule head. This means that the order in
which variables are bound affects whether the Formulog runtime accepts a rule or
not, even though different orders might be logically equivalent. For example,
this rule is disallowed, because the call to `f(X)` occurs syntactically before
the binding of `X` (given a left-to-right reading of the rule):

```
not_ok :- p(f(X)), p(X).
```

This rule would be accepted if it were rewritten as:

```
ok :- p(X), p(f(X)).
```

Similarly, the checker is overly conservative in its treatment of the `=`
predicate, rejecting rules that require "sub-unifications" to occur in an order
that is not left to right:

```
not_ok :- (_, X) = (f(X), 42).
```

Here, the second argument of the tuple needs to be unified before the first
argument can be. An equivalent rule would be accepted:

```
ok :- X = 42, _ = f(X).
```

In theory, Formulog could rewrite rules in situations like these to make it
easier to meet the binding requirements. It currently does not do so because
type checking is flow-sensitive, and so the runtime would need to ensure that
any rewriting results in a rule that is still well-typed. Although we have not
found our current approach to be a hindrance in practice, this is something that
we could implement in the future.

## Negation, aggregation, and stratification

To ensure that every program has a least model, Formulog requires the use of
stratified negation and aggregation, a common restriction in Datalog.
Intuitively, this restriction ensures that there are no recursive
negation/aggregation dependencies between predicates.

Since Formulog allows predicate symbols to appear in function bodies,
determining whether a Formulog program is stratified is slightly more
complicated than in the Datalog case. To determine if a program is stratified
we construct a dependence graph, where each node represents a different
predicate. There is a "positive" edge from a predicate `p` to a predicate `q`
if `p` appears in a positive atom in the body of a rule defining `q`. There is
a "negative" edge from `p` to `q` if `p` appears in a negated atom in the body
of a rule defining `q`, or `p` appears in the body of an expression that may be
transitively invoked from a rule defining `q`. A program is stratified if there
are no cycles in the dependence graph that include a "negative" edge.
