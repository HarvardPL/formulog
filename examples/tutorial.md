# Tutorial: Building a Refinement Type Checker

In this tutorial, we'll implement a type checker for a small (but still interesting) refinement type system in Formulog.
In particular, we'll implement the declarative type checking rules for the first system in the article [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763) by Ranjit Jhala and Niki Vazou.
Our hope is that our tutorial gives a good overview of many Formulog features, and a flavor of what it is like to program a nontrivial analysis in Formulog.

**Intended audience**:
This tutorial is intended for folks with some background with SMT solving, an ML-like functional language, and logic programming, as well as a level of comfort with formal programming language notation (like inference rules) -- so, essentially PL researchers and PL-oriented engineers.
It is recommended to skim the relevant sections in the article by Jhala and Vazou, as we'll be referring to their text often (and not repeating their exposition).

**Attribution**:
This tutorial includes figures from the article [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763) (v1) by Ranjit Jhala and Niki Vazou, which has been published under a [CC BY 4.0 license](https://creativecommons.org/licenses/by/4.0/).
We will refer to this article as "JV" for short.

## Help Improve This Tutorial

XXX

## General Approach

One of the claimed advantages of Datalog (for writing program analyses) is to be able to implement analysis logic at the level of mathematical specification.
Formulog extends this benefit to analyses that manipulate SMT formulas and rely on SMT solving for determining satisfiability.
Thus, our approach when implementing an analysis in Formulog is to try to directly translate the formal specification of an analysis---inference rules and (typically pure) helper functions---into Horn clauses and functions.
That is the approach we will follow in this tutorial: directly translate the formalism of JV as we encounter it, and then go back to patch our implementation as necessary.

We will work our way through JV Sections 3.1 and 3.2.
For the full, final code, see XXX.

## Definitions

The first formalism we encounter in JV Section 3.1 is a definition of types and environments (Figure 3.1), which also refers to the definitions of predicates (Figure 2.1).

We can encode these BNF-style definitions (along with the definition of constraints) using Formulog's support for algebraic data types:

```
(* An algebraic data type with a single variant *)
type basic_typ =
    | b_int

(* A type alias *)
type var = string

(* For the sake of simplicity, we'll support just a few operations *)
type op =
    | o_add
    | o_eq
    | o_mul

type pred =
    | p_var(var)
    | p_bool(bool)
    (* i32 is the type of a 32-bit signed integer *)
    | p_int(i32)
    | p_interp_op(op, pred, pred)
    | p_conj(pred, pred)
    | p_disj(pred, pred)
    | p_neg(pred)
    | p_ite(pred, pred, pred)

type constraint =
    | c_pred(pred)
    | c_conj(constraint, constraint)
    | c_imp(var, pred, constraint)

type typ =
    | t_refined(basic_typ, var, pred)
    | t_func(var, typ, typ)

type kind =
    | k_base
    | k_star

(* Tuples and lists are built-in type *)
type env = (var * typ) list
```

We can then similarly encode expressions, following Figure 3.2.

```
type expr =
    | e_int(i32)
    | e_var(var)
    | e_let(var, expr, expr)
    | e_lambda(var, expr)
    | e_app(expr, var)
    | e_annot(expr, typ)
```

### Well-formedness

The first judgments -- defining type well-formedness -- are given in Figure 3.3.

Typically, in Formulog, you would encode inference rules like these using Horn clauses, so let's do that here.

First, we need to declare a relation for well-formedness:

```
rel wf(env, typ, kind)
```

We can then encode the rules one by one, with reference to this relation.
Let's start with the simplest, Wf-Kind:

```
wf(G, T, k_star) :- wf(G, T, k_base).
```

Horn clauses are read right to left, so this rule is saying that types that are well-formed at kind base are also well-formed at kind star.
Identifiers beginning with an uppercase letter are logic programming variables.

Wf-Fun is not too bad to encode either:

```
wf(G, t_func(X, S, T), k_star) :-
    wf(G, S, _Ks),
    wf((X, S) :: G, T, _Kt).
```

Two things to note:

- Identifiers that begin with an underscore are anonymous variables. Formulog will reject rules where a non-anonymous variable only appears once (a common bug).
- The infix constructor `::` is the cons of a value and a list; in this case, we use it to extend the environment with a new binding (represented as a tuple).

Once we get to WF-Base, we notice that we're missing something: the premise requires the well-sortedness of a predicate, a judgment that is not defined in the paper.
The authors say that this amounts to standard type checking (with refinements ignored).
We'll have to declare a relation for this and encode the rules:

```
rel pred_wf(env, pred, basic_typ)
```

First, we might try to encode that a boolean value is, well, a boolean; to do so, we need to revise our definition of basic types to also include booleans:

```
(* Revised definition *)
type basic_typ =
    | b_int
    | b_bool
```

We can then encode the rule for boolean literals:

```
pred_wf(_E, p_bool(_B), b_bool).
```

The rules for most the other constructs is straightforward:

```
pred_wf(_E, p_int(_I), b_int).

pred_wf(E, p_interp_op(o_add, P1, P2), b_int) :-
    pred_wf(E, P1, b_int),
    pred_wf(E, P2, b_int).

pred_wf(E, p_interp_op(o_eq, P1, P2), b_bool) :-
    pred_wf(E, P1, T),
    pred_wf(E, P2, T).

(* We can define a Horn clause with two heads, meaning both conclusions hold *)
pred_wf(E, p_conj(P1, P2), b_bool),
pred_wf(E, p_disj(P1, P2), b_bool) :-
    pred_wf(E, P1, b_bool),
    pred_wf(E, P2, b_bool).

pred_wf(E, p_neg(P), b_bool) :-
    pred_wf(E, P, b_bool).

pred_wf(E, p_ite(P1, P2, P3), T) :-
    pred_wf(E, P1, b_bool),
    pred_wf(E, P2, T),
    pred_wf(E, P3, T).
```

The leaves us just handling variables; to do so, we need to define what it means to look up a variable in an environment.
Formulog's first-order functional programming comes in handy for defining this type of helper function:

```
fun lookup(x: var, e: env): typ option =
    match e with
    | [] => none
    | (y, t) :: rest => if x = y then some(t) else lookup(x, rest)
    end
```

The `option` type (with its constructors `none` and `some`) is built into Formulog.
We can now define the judgment for variables, as well as our final judgment for type well-formedness.

```
pred_wf(E, p_var(V), B) :-
    lookup(V, E) = some(t_refined(B, _, _)).

wf(G, t_refined(B, V, P), k_base) :-
    K = (V, t_refined(B, V, p_true)),
    pred_wf(K :: G, P, b_bool),
```

Note that in the `pred_wf` rule we invoke the `lookup` function we defined previously.

### Entailment and Subtyping

The next judgments we encounter in JV are those for entailment and subtyping (Figure 3.4).

The rule Ent-Emp requires us to determine if a constraint is valid; we can do this in Formulog by using the built-in function `is_valid`, provided that we convert a term of type `constraint` to a term of type `bool smt` (the type in Formulog representing an SMT proposition).
That doesn't sound too bad; we can write a function to do that.
The conjunction case is straightforward:

```
fun constraint2smt(c: constraint): bool smt =
    match c with
    | c_conj(c1, c2) =>
        let s1 = constraint2smt(c1) in
        let s2 = constraint2smt(c2) in
        `s1 /\ s2`
    (* TODO: other cases *)
    end
```

Note that SMT formulas are demarcated by backticks, and `/\` is the built-in notation for SMT conjunction.

Now let's consider another case in the match statement, corresponding to the constructor `c_pred(pred)`.
Here, we need to construct a term of type `bool smt` out of a term of type `pred`.
Let's try to do that in a helper function, `pred2smt`:

```
fun pred2smt(p: pred): bool smt =
    match p with
    (* Putting a term in quotes makes it type at the SMT level *)
    | p_bool(b) => `b`
    | p_conj(p1, p2) =>
        let b1 = pred2smt(p1) in
        let b2 = pred2smt(p2) in
        `b1 /\ b2`
    | p_disj(p1, p2) =>
        let b1 = pred2smt(p1) in
        let b2 = pred2smt(p2) in
        `b1 \/ b2`
    | p_neg(p1) => let b = pred2smt(p1) in `~b`
    | p_interp_op(o_eq, p1, p2) =>
        let b1 = pred2smt(p1) in
        let b2 = pred2smt(p2) in
        `b1 #= b2`
    (* TODO: other cases *)
    end
```

So far, so good.
But how about when we get to the `p_int` case?
The function signature requires us to return a term of type `bool smt`, but that doesn't make any sense in this case.
In fact, if we take a closer look at how predicates are defined, we can see that the syntax for predicates allow bool-valued and int-valued terms to be mixed.
We could go back, and try to redefine the syntax for predicates in a way that distinguishes between bool-valued and int-valued terms.
However, even if this were possible, doing so would have a few downsides.
First, it takes us farther away from the formalism of JV.
Second, it would likely lead to duplication, since we would need, e.g., two different constructors for equality, one where the subterms are ints and one where the subterms are bools.
Third, it does not seem like a very flexible approach as our language of predicates becomes more complex.

There is another alternative, which is to push the bool-vs-int distinction into the SMT level, using the SMT theory of algebraic data types (this follows Dminor XXX).
To do so, we'll define a new algebraic data type, representing a value in a predicate:

```
type val =
    | v_int(int)
    | v_bool(bool)
```

This type will only appear in SMT formulas.
We can then redefine `pred2smt` to return a term of type `val smt` (instead of `bool smt`):

```
fun pred2smt(p: pred): val smt =
    match p with
    | p_bool(b) => `v_bool(b)`
    | p_conj(p1, p2) =>
        let v1 = pred2smt(p1) in
        let v2 = pred2smt(p2) in
        `v_bool(#v_bool_1(v1) /\ #v_bool_1(v2))`
    | p_disj(p1, p2) =>
        let v1 = pred2smt(p1) in
        let v2 = pred2smt(p2) in
        `v_bool(#v_bool_1(v1) \/ #v_bool_1(v2))`
    | p_neg(p1) =>
        let v1 = pred2smt(p1) in
        `v_bool(~#v_bool_1(v1))`
    | p_int(n) => `v_int(int_const(n))`
    | p_interp_op(o, p1, p2) =>
        let v1 = pred2smt(p1) in
        let v2 = pred2smt(p2) in
        match o with
        | o_eq => `v_bool(v1 #= v2)`
        | o_add => `v_int(int_add(#v_int_1(v1), #v_int_1(v2)))`
        end
    | p_ite(p1, p2, p3) =>
        let v1 = pred2smt(p1) in
        let v2 = pred2smt(p2) in
        let v3 = pred2smt(p3) in
        `#if #v_bool_1(v1) then v2 else v3`
    | p_var(x) => `#{x}[val]`
    end
```

There's a lot going on here.
Let's look at some simple cases first.

- `` p_bool(b) => `v_bool(b)` ``: We have a term `b` of type `bool`; to turn it into a term of type `val`, we wrap it in the constructor `v_bool`; to turn this into a term of type `val smt`, we quote it with backticks.
- `` p_int(n) => `v_int(int_const(n))` ``: We have a term `n` of type `i32`; we can turn it into a term of type `int smt` (a mathematical integer in SMT land) by wrapping it with the constructor `int_const`, and then supply this term as an argument to the `v_int` constructor to create a term of type `val smt`. Note that even though the `v_int` constructor is defined to take a term of type `int` and not `int smt`, the two types are conflated when occurring within an SMT formula (i.e., between backticks).
- `` p_var(x) => `#{x}[val]` ``: we take a predicate-level variable `x` and construct an SMT-level variable named `x` that is typed as `val` within the SMT formula. Technically, the syntax `#{x}[val]` creates a Formulog term of type `val sym` (i.e., a `val`-valued SMT variable), and the backticks then raise the type to `val smt`.

In the other cases, we see the use of the constructors `#v_int_1` and `#v_bool_1`.
For all datatypes (that can be expressed at the SMT level), Formulog creates constructors of this form that can be used within SMT formulas to access the arguments of constructors.
For example, `#v_int_1` is defined so that `#v_int_1(v_int(X))` is the int `X`, but `#v_int_1(v_bool(_))` is any int.
This approach reflects the SMT-LIB theory of algebraic datatypes.
Essentially, these constructors allow us to coerce (within an SMT formula) a value of type `val` to a `bool` or `int`.

Now that we have `pred2smt`, we can go back and finish our definition of `constraint2smt`:

```
fun constraint2smt(c: constraint): bool smt =
    match c with
    | c_conj(c1, c2) =>
        let s1 = constraint2smt(c1) in
        let s2 = constraint2smt(c2) in
        `s1 /\ s2`
    | c_pred(p) => let s = pred2smt(p) in `#v_bool_1(s)`
    | c_imp(x, p1, c1) =>
        let prem = pred2smt(p1) in
        let conl = constraint2smt(c1) in
        `forall #{x}[val]. #v_bool_1(prem) ==> conl`
    end
```

### Type Synthesis

### Type Checking

- [ ] Add uninterpreted function to expressions
- [ ] Support bools
- [ ] Dminor
- [ ] Precision of typed SMT terms
- [ ] Why not represent preds, constraints with SMT terms to begin with? Checking well-formedness trickier