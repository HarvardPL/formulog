# Logical formulas

Formulog provides support for representing and reasoning about logical
formulas.

## Example

This example program would produce the facts `ok1`, `ok2`, and `ok3`.

```
output ok1
ok1 :-
  is_valid(`false ==> true`),
  !is_sat(`true ==> false`).

output ok2
ok2 :-
  E = `bv_add(#x[bv[32]], 42) #= 0`,
  is_sat(E),
  F = `bv_sge(#x[bv[32]], 0)`,
  is_sat(F),
  !is_sat(`E /\ F`).

type 'a my_list =
  | my_nil
  | my_cons('a, 'a my_list)

output ok3.
ok3 :-
  Xs = #xs[bool my_list],
  Ys = #ys[bool my_list],
  E = `Xs #= my_cons(true, Ys)`,
  is_sat(E),
  F = `#is_my_nil(Xs)`,
  is_sat(F),
  !is_sat(`E /\ F`).
```

## Formula types

For every non-formula type τ, there are two corresponding types that
are used to represent τ-valued logical formulas. The first is `τ smt`, which
represents a τ-valued formula. The second is `τ sym`, which represents a
τ-valued formula variable (it is sometimes helpful to distinguish between these
two types).

Outside of logical formulas, the types τ, `τ smt`, and `τ sym` are treated as
being distinct. However, within a formula, they are treated as being all the
same type. This bimodal type checking makes it easy to write expressive
formulas, while making sure that evaluation outside of formulas does not get
stuck.

Formulog also supports uninterpreted sorts that can be used within formulas.
For instance, you can declare a polymorphic uninterpreted sort like this:

```
uninterpreted sort ('a, 'b) foo.
```

## Representing formulas

Formulas are constructed from a library of constructors and are typically
quoted by backticks, which tells the type checker to use the "formula mode" of
the bimodal type system. Function calls that take arguments cannot appear
within quotations.

### Formula variables

Formulog distinguishes between logic programming variables (like `X`) and
formula variables (like `#x[bool]`). The latter are only interpreted as
variables within formula; otherwise they are ground terms. Formula variables
can be created using a special syntax: a pound sign, followed by a term `t`
of arbitrary type within curly braces, followed by a type τ within square
brackets, as in
```
#{t}[τ]
```
τ cannot have any type variables and cannot contain any formula types (like
`sym` or `smt`). The term `t` is the "name" of the formula variable.

A formula variable will unify with another formula variable only if they have
the same "name" and type. For example,
```
`#{42}[bool] = #{"hello"}[bool]`
```
never holds, although the formula
```
`#{42}[bool] #= #{"hello"}[bool]`
```
is satisfiable. **Note that a formula variable `#{t}[τ]` is guaranteed to not
unify with any subterm of `t`; that is, it is fresh for `t`.**

There is also a shorthand syntax: a pound sign, followed by an identifier
(beginning with a lowercase letter), followed by a type within square brackets,
as in `#x[bool]`. This is the same thing as `#{"x"}[bool]`.

Every variable occurring in the argument to a formula variable must be bound
elsewhere.

### Built-in formula terms

Formulog provides built-in terms that are used to construct formulas that
should be interpreted under a particular theory.

#### Logical connectives

For instance, we have basic logical connectives:
```
~ [...]                         : bool smt -> bool smt
[...] #= [...]                  : ('a smt, 'a smt) -> bool smt
[...] /\ [...]                  : (bool smt, bool smt) -> bool smt
[...] \/ [...]                  : (bool smt, bool smt) -> bool smt
[...] ==> [...]                 : (bool smt, bool smt) -> bool smt
[...] <==> [...]                : (bool smt, bool smt) -> bool smt
#if [...] then [...] else [...] : (bool smt, 'a smt, 'a smt) -> 'a smt
#let [...] = [...] in [...]     : ('a sym, 'a smt, 'b smt) -> 'b smt
```
The binary operators are listed above in order of precedence (so `#=`
binds the most tightly, and `<==>` the least tightly). They all associate
to the right, except for `#=`, which associates to the left.

We also have quantifiers `forall` and `exists`, as in this example:
```
  `forall #x[bool]. exists #y[bool]. #x[bool] #= ~#y[bool]`
```
They can bind multiple variables:
```
  `exists #x[bool], #y[bool]. #x[bool] #= ~#y[bool]`
```
You can also specify patterns for trigger-based instantiation. For example, say
that `f` is an uninterpreted function from bools to bools. This formula says
that `f(x) = x` for all `x`, using `f(x)` as a trigger:
```
  `forall #x[bool] : f(#x[bool]). f(#x[bool]) #= #x[bool]`
```
Multiple patterns are also supported; they should be separated by commas.

#### Bit vectors

We have bit vectors, where `k` is a positive integer specifying the bit
vector width:
```
bv_const[k](i32)
bv_big_const[k] : i64 -> bv[k] smt
bv_neg : bv[k] smt -> bv[k] smt
bv_add : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_sub : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_mul : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_sdiv : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_srem : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_and : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_or : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_xor : (bv[k] smt, bv[k] smt) -> bv[k] smt
bv_to_bv_signed[k] : bv[_] smt -> bv[k] smt
bv_to_bv_unsigned[k] : bv[_] smt -> bv[k] smt
fp_to_bv[k] : fp[_,_] smt -> bv[k] smt
bv_lt : (bv[k] smt, bv[k] smt) -> bool smt
bv_le : (bv[k] smt, bv[k] smt) -> bool smt
bv_gt : (bv[k] smt, bv[k] smt) -> bool smt
bv_ge : (bv[k] smt, bv[k] smt) -> bool smt
```
Note that some of these constructors are indexed, as in `bv_const[k](i32)`.
This means that a width needs to explicitly provided, as in `bv_const[16](42)`,
which constructs a bit vector constant with width 16 and value 42.

#### Floating point

And we have floating point, where `j` and `k` are positive integers specifying,
respectively, the exponent length and significand length:
```
fp_const[j,k] : fp32 -> fp[j,k] smt
fp_big_const[j,k] : fp64 -> fp[j,k] smt
fp_neg : fp[j,k] smt -> fp[j,k] smt
fp_add : (fp[j,k] smt, fp[j,k] smt) -> fp[j,k] smt
fp_sub : (fp[j,k] smt, fp[j,k] smt) -> fp[j,k] smt
fp_mul : (fp[j,k] smt, fp[j,k] smt) -> fp[j,k] smt
fp_div : (fp[j,k] smt, fp[j,k] smt) -> fp[j,k] smt
fp_rem : (fp[j,k] smt, fp[j,k] smt) -> fp[j,k] smt
fp_to_fp[j,k] : fp[_,_] smt -> fp[j,k] smt
bv_to_fp[j,k] : bv[_] smt -> fp[j, k] smt
fp_lt : (fp[j,k] smt, fp[j,k] smt) -> bool smt
fp_le : (fp[j,k] smt, fp[j,k] smt) -> bool smt
fp_gt : (fp[j,k] smt, fp[j,k] smt) -> bool smt
fp_ge : (fp[j,k] smt, fp[j,k] smt) -> bool smt
fp_is_nan : fp[j,k] smt -> bool smt
fp_eq : (fp[j,k] smt, fp[j,k] smt) -> bool smt
```
To make it syntactically more pleasant to deal with common floating point
types, we provide the following shorthand:
* the index `[5,11]` can be written as `[16]`;
* the index `[8,24]` can be written as `[32]`;
* the index `[11,53]` can be written as `[64]`; and
* the index `[15,113]` can be written as `[128]`.

#### Integers

```
int_abs : int smt -> int smt
int_neg : int smt -> int smt
int_const : bv[32] -> int smt
int_big_const : bv[64] -> int smt
int_ge : int smt, int smt -> bool smt
int_gt : int smt, int smt -> bool smt
int_le : int smt, int smt -> bool smt
int_gt : int smt, int smt -> bool smt
int_add : int smt, int smt -> int smt
int_mul : int smt, int smt -> int smt
int_mod : int smt, int smt -> int smt
int_sub : int smt, int smt -> int smt
int_div : int smt, int smt -> int smt
```

#### Arrays

```
array_select : ('a, 'b) array smt, 'a smt -> 'b smt 
array_store : ('a, 'b) array smt, 'a smt, 'b smt -> ('a, 'b) array smt
array_default : ('a, 'b) array smt -> 'b smt
array_const : 'b smt -> ('a, 'b) array smt
```

#### Strings

```
str_at : string smt, int smt -> string smt
str_concat : string smt, string smt -> string smt
str_contains : string smt, string smt -> bool smt
str_indexof : string smt, string smt, int smt -> int smt
str_len : string smt -> int smt
str_prefixof : string smt, string smt -> bool smt
str_replace : string smt, string smt, string smt -> string smt
str_substr : string smt, int smt, int smt -> string smt
str_suffixof : string smt, string smt -> bool smt
```

### Using algebraic data types and records in formulas

Terms constructed from user-defined algebraic data types can also be used in
formulas, where they are interpreted under the theory of algebraic data types.
Say we define this type:
```
type 'a my_list =
  | my_nil
  | my_cons('a, 'a my_list)
```
In addition to being able to use the constructors `my_nil` and `my_cons` within
a formula, one can also use constructors that are automatically generated by
Formulog and that make it easier to state formula about `my_list` terms:
```
#is_my_nil : 'a my_list smt -> bool smt
#is_my_cons : 'a my_list smt -> bool smt
#my_cons_1 : 'a my_list smt -> 'a smt
#my_cons_2 : 'a my_list smt -> 'a my_list smt
```
These automatically generated constructors fall into two categories: testers,
which are identified by the prefix `#is_` followed by the name of the
constructor and are used to test the outermost constructor of a (possibly
symbolic) term, and getters, which are identified by the name of the
constructor prefixed with a `#` and followed by an underscore and an argument
position, and which are used to extract the argument of a (possibly symbolic)
term.

Symbolic getters are also created for records, where each getter is the name of
the relevant label prefixed with `#`.

### Uninterpreted functions

Formulog also provides a way to declare uninterpreted functions, as here:
```
uninterpreted fun foo(bv[32] smt) : bool smt
```
This effectively defines a new constructor for `bool smt` that expects a
single argument of type `bv[32] smt`. Uninterpreted functions can only be used
within formulas.

## Reasoning about formulas

Formulog currently provides these functions for reasoning about/manipulating
formulas:
```
is_sat : bool smt -> bool
is_sat_opt : (bool smt, i32 option) -> bool option
is_valid : bool smt -> bool
is_valid_opt : (bool smt, i32 option) -> bool option
get_model : (bool smt, i32 option) -> model option
query_model : ('a sym, model) -> 'a option
substitute : ('a sym, 'a smt, 'b smt) -> 'b smt
is_free : ('a sym, 'b smt) -> bool
```

The functions `is_sat` and `is_valid` check the satisfiability and validity,
resp., of their argument and throw an exception if the SMT solver returns
`unknown`. The functions `is_sat_opt` and `is_valid_opt` return `none` in this
case; they also take an argument for an optional timeout.

The function takes a proposition and an optional timeout and returns a model
for that proposition if the SMT solver finds one in time; it returns `none`
otherwise.
Variables in a model can be inspected using `query_model`, which will return
`none` if a variable is not present in the model or if it is of a type that
cannot be concretely represented in Formulog (for example, Formulog does not
have a concrete representation of a 13-bit bit vector).

The function `substitute` is capture avoiding (for instance, it handles `let`
expressions correctly within formulas). The function `is_free` returns true iff
the given formula variable appears free in the supplied formula.
