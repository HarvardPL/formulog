# Logical formulas

Formulog provides support for representing and reasoning about logical formulas.

## Example

This example program would produce the facts `ok1`, `ok2`, and `ok3`.

```
rel ok1
ok1 :-
  is_valid(`false ==> true`),
  !is_sat(`true ==> false`).

rel ok2
ok2 :-
  E = `bv_add(#x[bv[32]], 42) #= 0`,
  is_sat(E),
  F = `bv_sge(#x[bv[32]], 0)`,
  is_sat(F),
  !is_sat(`E /\ F`).

type 'a my_list =
  | my_nil
  | my_cons('a, 'a my_list)

rel ok3
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

For every non-formula type τ, there are two corresponding types that are used to
represent τ-valued logical formulas. The first is `τ smt`, which represents a
τ-valued formula. The second is `τ sym`, which represents a τ-valued formula
variable (it is sometimes helpful to distinguish between these two types).

You will often see formulas quoted with backticks, as in

```
`#x[bool] #= true`
```

Quoted terms are type checked differently than terms outside of quotations.
Outside of quotations, the types τ, `τ smt`, and `τ sym` are treated as being
distinct. However, in quoted terms, they are treated as being all the same type.
This bimodal type checking makes it easy to write expressive formulas, while
making sure that evaluation outside of formulas does not get stuck, which might
happen if a boolean formula were passed to a function expecting a concrete
boolean argument.

The Formulog type sensitive is flow-sensitive, in that the order of the atoms
and terms in a rule affect whether that rule is considered well typed or not.
For example, it rejects the first rule in this program and not the second, even
though they are logically equivalent:

```
rel p(bool smt)
rel q(bool)
rel not_ok
rel ok

not_ok :- p(`X`), q(X).
ok     :- q(X), p(`X`).
```

It rejects the first rule because, given a left-to-right reading of the rule,
`X` is bound in a position that has type `bool smt`, and so there is no
guarantee it is a concrete `bool` (which would be required for it to be a member
of `q`). The second rule is fine since `X` is bound in a position that has type
`bool`, which becomes a `bool smt` when it is quoted as an argument to `p`. The
type checker currently uses the order that the rule was originally written; in
the future, the type checker could try to reorder rules to make them well typed.

### Uninterpreted sorts

Formulog allows users to define uninterpreted sorts that can be used within
formulas. For instance, you can declare a polymorphic uninterpreted sort like
this:

```
uninterpreted sort ('a, 'b) foo
```

## Representing formulas

Formulas are constructed from a library of constructors and are typically quoted
by backticks, which tells the type checker to use the "formula mode" of the
bimodal type system. Function calls that take arguments cannot appear within
quotations.

### Formula variables

Formulog distinguishes between logic programming variables (like `X`) and
formula variables (like `#x[bool]`). The latter are only interpreted as
variables within formula; otherwise they are ground terms. Formula variables can
be created using a special syntax: a pound sign, followed by a term `t`
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
#{42}[bool] = #{"hello"}[bool]
```

never holds, although the formula

```
`#{42}[bool] #= #{"hello"}[bool]`
```

is satisfiable (where `#=` is the notation for formula equality). **Note:** A
formula variable `#{t}[τ]` is guaranteed to not unify with any subterm of `t`;
that is, it is fresh for `t`.

There is also a shorthand syntax: a pound sign, followed by an identifier,
followed by a type within square brackets, as in `#x[bool]`. This is the same
thing as `#{"x"}[bool]`.

### Built-in formula terms

Formulog provides built-in terms that are used to construct formulas that should
be interpreted under a particular theory. For the most part, these constructors
directly reflect the SMT-LIB standard.

#### Parameterized terms

You will see that many formula terms are parameterized with a type or natural
number. For example, the constructor for formula equality, `smt_eq[τ]`, is
parameterized with the type τ of the operands of the equality, and the
constructor for a bit vector constant, `bv_const[k]`, is parameterized with the
width `k` of the bit vector. These parameters are necessary either because the
type information is important to have at runtime (when serializing formulas into
SMT-LIB), or for type safety reasons (issues arise if the type of the term does
not uniquely determine the types of its arguments). However, Formulog can often
infer the correct type without an explicit annotation. If you leave out the
square brackets, Formulog will try to infer every parameter for that term;
alternatively, select parameters can be inferred by using the wildcard parameter
`?`. For example, these formulas all say the same thing:

```
`smt_eq[bv[32]](bv_const[32](42), 0)`
`smt_eq[?](bv_const[?](42), 0)`
`smt_eq(bv_const(42), 0)`
```

Formulog can infer that this is a comparison of 32-bit bit vectors from the fact
that the second operand is the constant `0`, which has type `bv[32]`. However,
the following formulas are unacceptable, since Formulog cannot infer the widths
of the bit vectors in the comparisons:

```
`smt_eq[?](bv_const[?](42), bv_const[?](0))`
`smt_eq(bv_const(42), bv_const(0))`
```

In this case, one annotation is enough to clarify things:

```
`smt_eq[bv[32]](bv_const(42), bv_const(0))`
`smt_eq(bv_const[32](42), bv_const(0))`
```

The parameters to a parameterized constructor have to be fully resolved at
compile time.

#### Logical connectives

Formulog has the standard first-order logic connectives:

```
smt_not    : bool smt -> bool smt
smt_eq[τ]  : [τ smt, τ smt] -> bool smt
smt_and    : [bool smt, bool smt] -> bool smt
smt_or     : [bool smt, bool smt] -> bool smt
smt_imp    : [bool smt, bool smt] -> bool smt
smt_ite    : [bool smt, 'a smt, 'a smt] -> 'a smt
smt_let[τ] : [τ sym, τ smt, 'a smt] -> 'a smt
smt_exists : [smt_wrapped_var list, bool smt, smt_pattern list list] -> bool smt
smt_forall : [smt_wrapped_var list, bool smt, smt_pattern list list] -> bool smt
```

The quantifiers deserve some explanation. The first argument is a list of
"wrapped" formula variables bound by the quantifier; the type `smt_wrapped_var`
has a single constructor:

```
smt_wrap_var[τ] : τ sym -> smt_wrapped_var
```

The second argument is the body of the quantifier. The third and final argument
represents a list of patterns to supply for trigger-based quantifier
instantiation. Each member of the outermost list represents a single pattern,
possibly consisting of multiple terms. The type `smt_pattern` has a single
constructor:

```
smt_pat[τ] : τ -> smt_pattern
```

However, it is unlikely that you will have to use these constructors directly,
as we supply notation that should cover most situations:

```
~ ...                     (* negation *) 
... #= ...                (* equality *)
... /\ ...                (* conjunction *) 
... \/ ...                (* disjunction *)
... ==> ...               (* implication *)
... <==> ...              (* iff *)
#if ... then ... else ...
#let ... = ... in ... 
```

The binary operators are listed above in order of precedence (so `#=`
binds the most tightly, and `<==>` the least tightly). They all associate to the
right, except for `#=`, which associates to the left.

There is also notation for the quantifiers `forall` and `exists`, as in this
example:

```
  `forall #x[bool]. exists #y[bool]. #x[bool] #= ~#y[bool]`
```

The notation supports binding multiple variables:

```
  `exists #x[bool], #y[bool]. #x[bool] #= ~#y[bool]`
```

You can also specify patterns for trigger-based instantiation. For example, say
that `f` is an uninterpreted function from bools to bools. This formula says
that `f(x) = x` for all `x`, using `f(x)` as a trigger:

```
  `forall #x[bool] : f(#x[bool]). f(#x[bool]) #= #x[bool]`
```

The notation supports patterns with multiple terms (they should be separated by
commas); however, it does not support multiple patterns, in which case you need
to use the explicit constructor described above.

#### Bit vectors

We have bit vectors, where `bv[k] smt` is a `k`-bit symbolic bit vector:

```
bv_const[k]            : bv[32] -> bv[k] smt
bv_big_const[k]        : bv[64] -> bv[k] smt
bv_neg                 : bv[k] smt -> bv[k] smt
bv_add                 : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_sub                 : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_mul                 : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_sdiv                : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_srem                : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_and                 : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_or                  : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_xor                 : [bv[k] smt, bv[k] smt] -> bv[k] smt
bv_to_bv_signed[j,k]   : bv[j] smt -> bv[k] smt
bv_to_bv_unsigned[j,k] : bv[j] smt -> bv[k] smt
fp_to_sbv[i,j,k]       : fp[i,j] smt -> bv[k] smt
fp_to_ubv[i,j,k]       : fp[i,j] smt -> bv[k] smt
bv_slt[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_sle[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_sgt[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_sge[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_ult[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_ule[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_ugt[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_uge[k]              : [bv[k] smt, bv[k] smt] -> bool smt
bv_extract[j,k]        : [bv[j] smt, i32, i32] -> bv[k] smt
bv_concat[i,j,k]       : [bv[i] smt, bv[j] smt] -> bv[k] smt
```

Note that in some cases the bit vector width is a parameter to the constructor;
as noted previously, parameters can often be inferred.

The `bv_extract` and `bv_concat` constructors currently do not enforce some
constraints on their parameters (for example, with `bv_concat[i,j,k]`, it must
be that `i + j = k`). Illegal parameter choices are therefore not caught by the
type system, and might lead to SMT solver crashes at runtime.

#### Floating point

And we have floating point, where `fp[j,k] smt` is a symbolic floating point
number with exponent length `j` and signficand length `k`:

```
fp_const[j,k]     : fp[32] -> fp[j,k] smt
fp_big_const[j,k] : fp[64] -> fp[j,k] smt
fp_neg            : fp[j,k] smt -> fp[j,k] smt
fp_add            : [fp[j,k] smt, fp[j,k] smt] -> fp[j,k] smt
fp_sub            : [fp[j,k] smt, fp[j,k] smt] -> fp[j,k] smt
fp_mul            : [fp[j,k] smt, fp[j,k] smt] -> fp[j,k] smt
fp_div            : [fp[j,k] smt, fp[j,k] smt] -> fp[j,k] smt
fp_rem            : [fp[j,k] smt, fp[j,k] smt] -> fp[j,k] smt
fp_to_fp[h,i,j,k] : fp[h,i] smt -> fp[j,k] smt
bv_to_fp[i,j,k]   : bv[i] smt -> fp[j, k] smt
fp_lt[j,k]        : [fp[j,k] smt, fp[j,k] smt] -> bool smt
fp_le[j,k]        : [fp[j,k] smt, fp[j,k] smt] -> bool smt
fp_gt[j,k]        : [fp[j,k] smt, fp[j,k] smt] -> bool smt
fp_ge[j,k]        : [fp[j,k] smt, fp[j,k] smt] -> bool smt
fp_is_nan[j,k]    : fp[j,k] smt -> bool smt
fp_eq[j,k]        : [fp[j,k] smt, fp[j,k] smt] -> bool smt
```

To make it syntactically more pleasant to deal with common floating point types,
instead of supplying both the exponent and significand length, users can supply
a single parameter that is expanded into the appropriate exponent and
significand:

* the parameter `16` is expanded to `5,11`;
* the parameter `32` is expanded to `8,24`;
* the parameter `64` is expanded to `11,53`; and
* the parameter `128` is expanded to `15,113`.

For example, the term `fp_const[32](...)` is equivalent to
`fp_const[8,24](...)`.

#### Integers

Mathematical integers are represented by the type `int smt`:

```
int_abs       : int smt -> int smt
int_neg       : int smt -> int smt
int_const     : bv[32] -> int smt
int_big_const : bv[64] -> int smt
int_ge        : [int smt, int smt] -> bool smt
int_gt        : [int smt, int smt] -> bool smt
int_le        : [int smt, int smt] -> bool smt
int_lt        : [int smt, int smt] -> bool smt
int_add       : [int smt, int smt] -> int smt
int_mul       : [int smt, int smt] -> int smt
int_mod       : [int smt, int smt] -> int smt
int_sub       : [int smt, int smt] -> int smt
int_div       : [int smt, int smt] -> int smt
int_to_bv[k]  : int smt -> bv[k] smt
bv_to_int[k]  : bv[k] smt -> int smt
```

Note that `int_to_bv[k]` and `bv_to_int[k]` do not correspond to any operations
in the SMT-LIB standard. These are serialized as `int2bv` and `bv2int`
operations, which are supported by Z3, but not by some other solvers.

#### Arrays

Arrays from `'a` to `'b` are represented by the type `('a, 'b) array smt`:

```
array_select[τ]  : [(τ, 'a) array smt, τ smt] -> 'a smt 
array_store      : [('a, 'b) array smt, 'a smt, 'b smt] -> ('a, 'b) array smt
array_default[τ] : (τ, 'a) array smt -> 'a smt
array_const      : 'b smt -> ('a, 'b) array smt
```

#### Strings

Symbolic strings are represented by the type `string smt`:

```
str_at       : string smt, int smt -> string smt
str_concat   : string smt, string smt -> string smt
str_contains : string smt, string smt -> bool smt
str_indexof  : string smt, string smt, int smt -> int smt
str_len      : string smt -> int smt
str_prefixof : string smt, string smt -> bool smt
str_replace  : string smt, string smt, string smt -> string smt
str_substr   : string smt, int smt, int smt -> string smt
str_suffixof : string smt, string smt -> bool smt
```

These operations follow the theory of strings supported by Z3 and CVC4.

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
Formulog and that make it easier to state formulas about `my_list` terms:

```
#is_my_nil  : 'a my_list smt -> bool smt
#is_my_cons : 'a my_list smt -> bool smt
#my_cons_1  : 'a my_list smt -> 'a smt
#my_cons_2  : 'a my_list smt -> 'a my_list smt
```

These automatically generated constructors fall into two categories: testers,
which are identified by the prefix `#is_` followed by the name of the
constructor and are used to test the outermost constructor of a (possibly
symbolic) term, and getters, which are identified by the name of the constructor
prefixed with a `#` and followed by an underscore and an argument position, and
which are used to extract the argument of a (possibly symbolic)
term.

Symbolic getters are also created for records, where each getter is the name of
the relevant label prefixed with `#`.

### Uninterpreted functions

Formulog also provides a way to declare uninterpreted functions, as here:

```
uninterpreted fun foo(bv[32] smt) : bool smt
```

This effectively defines a new constructor for `bool smt` that expects a single
argument of type `bv[32] smt`. Uninterpreted functions can only be used within
formulas.

## Reasoning about formulas

Formulog currently provides these functions for reasoning about/manipulating
formulas:

```
is_sat       : bool smt -> bool
is_sat_opt   : [bool smt list, i32 option] -> bool option
is_valid     : bool smt -> bool
get_model    : [bool smt list, i32 option] -> model option
query_model  : ['a sym, model] -> 'a option
substitute   : ['a sym, 'a smt, 'b smt] -> 'b smt
is_free      : ['a sym, 'b smt] -> bool
```

The functions `is_sat` and `is_valid` check the satisfiability and validity,
resp., of their argument and throw an exception if the SMT solver returns
`unknown`. The function `is_sat_opt` takes a list of propositions and checks for
the satisfiability of their conjunction, returning `none` in the case of
`unknown`; it also takes an argument for an optional timeout.

The function `get_model` takes a list of propositions and an optional timeout
and returns a model for the conjunction of those propositions if the SMT solver
finds one in time; it returns `none` otherwise. Variables in a model can be
inspected using `query_model`, which will return
`none` if a variable is not present in the model or if it is of a type that
cannot be concretely represented in Formulog (for example, Formulog does not
have a concrete representation of a 13-bit bit vector).

The function `substitute` is capture avoiding (for instance, it handles `let`
expressions correctly within formulas). The function `is_free` returns true iff
the given formula variable appears free in the supplied formula.
