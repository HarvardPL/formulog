# Tutorial: Building a Refinement Type Checker

In this tutorial, we'll implement a type checker for a small (but still interesting) refinement type system in Formulog.
In particular, we'll implement the declarative type checking rules for the first system in the article [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763) by Ranjit Jhala and Niki Vazou.
Our hope is that our tutorial gives a good overview of many Formulog features, and a flavor of what it is like to program a nontrivial analysis in Formulog.

**Intended audience**:
This tutorial is intended for folks with some background with SMT solving, an ML-like functional language, and logic programming, as well as a level of comfort with formal programming language notation (like inference rules).

**Attribution**:
This tutorial includes figures from the article [Refinement Types: A Tutorial](https://arxiv.org/abs/2010.07763) (v1) by Ranjit Jhala and Niki Vazou, which has been published under a [CC BY 4.0 license](https://creativecommons.org/licenses/by/4.0/).
We will refer to this article as "JV" for short.

## General Approach

One of the claimed advantages of Datalog (for writing program analyses) is to be able to implement analysis logic at the level of mathematical specification.
Formulog extends this benefit to analyses that manipulate SMT formulas and rely on SMT solving for determining satisfiability.
Thus, our approach when implementing an analysis in Formulog is to try to directly translate the formal specification of an analysis---inference rules and (typically pure) helper functions---into Horn clauses and functions.
That is the approach we will follow in this tutorial: directly translate the formalism of JV as we encounter it, and then go back to patch our implementation as necessary.

We will work our way through JV Sections 3.1 and 3.2.

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
    | c_imp(var, basic_typ, pred, constraint)

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

### Entailment and subtyping

### Type Synthesis

### Type Checking

- [ ] Add uninterpreted function to expressions
- [ ] Support bools