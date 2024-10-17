---
title: Language Basics
layout: page
parent: Language Reference
nav_order: 1
---

# Language Basics

Formulog is an extension of Datalog designed to support program analyses that
use logical formulas, such as symbolic execution and refinement type checking.

A Formulog program consists of three main components:

* type definitions;
* relation declarations and definitions; and
* function definitions.

## Types

Formulog has a strong, static type system.

### Built-in Types

Formulog has five built-in primitive types:

* booleans (`bool`), i.e., `true` and `false`;
* signed 32-bit integers (`i32` or equivalently `bv[32]`), as in `42`;
* signed 64-bit integers (`i64` or equivalently `bv[64]`), as in `42L`;
* 32-bit floating point numbers (`fp32` or equivalently `fp[8,24]`), as in
  `42.0F`;
* 64-bit floating point numbers (`fp64` or equivalently `fp[11,53]`), as
  in `42.0`
  or `42.0D`; and
* string constants (`string`), as in `"hello"`.

Beyond these primitive types, Formulog provides the following built-in algebraic
data types:

```
type 'a list =
  | nil
  | cons('a, 'a list)

type 'a option =
  | none
  | some('a)

type cmp =
  | cmp_lt
  | cmp_eq
  | cmp_gt
```

It also has built-in types representing logical formulas, but a discussion of
these is delayed until the [section on logical formulas]({{ site.baseurl }}{% link lang_ref/logical_formulas.md %}).

#### List Notation

Formulog provides special notation for terms of the `list` type. The `cons`
constructor can be written using the infix notation `::`; i.e., `X :: Y` is
shorthand for `cons(X, Y)`. A list can also be written as a sequence of
comma-separated elements between a pair of square brackets. For example, the
term `[X, Y, Z]` is shorthand for `cons(X, cons(Y, cons(Z, nil)))`. The term
`[]` is `nil`, the empty list.

Both notations can be used in pattern matching (described below).

### User-Defined Types

Formulog allows users to define their own (polymorphic) algebraic data types.
For instance, this defines a list-like type:

```
type 'a my_list =
  | my_nil
  | my_cons('a, 'a my_list)
```

Like types, constructors must begin with a lowercase letter.

Formulog also has support for tuple types, such as the type `i32 * string`, and
users can also define type aliases, such as this one that defines a map to be an
association list:

```
type ('k, 'v) map = ('k * 'v) my_list
```

Mutually recursive types are written using `and`:

```
type foo =
  | foo1
  | foo2(bar)
and bar =
  | bar1(foo)
  | bar2(bar, bar)
```

You can also define records, as here:

```
type 'a linked_list = {
  val  : 'a;
  next : 'a linked_list option;
}
```

Labels must be valid identifiers and cannot be shared across other types. For
each label, Formulog will automatically generate a function with that name that
extracts the relevant value from the record. For example, in the case of
`linked_list`, Formulog will generate:

```
val  : 'a linked_list -> 'a
next : 'a linked_list -> 'a linked_list option
```

Formulog also supports OCaml-style functional record update, as in this example:

```
type point3d = { x : i32; y : i32; z : i32 }
fun foo : i32 =
  let X = { x = 1; y = 2; z = 3 } in
  let Y = { X with x = -1; z = 0 } in
  x(Y) + y(Y) + z(Y)
```

A call `foo` would evaluate to the value `1`.

## Relations

In Formulog, relations are declared using the keyword `rel`, followed by the
name of the relation, and the types of the relation arguments. Relation
arguments can also be given labels (as documentation):

```
rel foo(i32, string)
rel pair(first: i32, second: i32) (* `first` and `second` are labels *)
```

Some relations are defined only in terms of explicitly enumerated facts. This
one relates pairs of nodes and consists of three pairs:

```
type node = string
rel edge(node, node)
edge("a", "b").
edge("b", "c").
edge("c", "b").
```

Relations like this—that consist only of enumerated facts—can be annotated with
the `@edb` annotation, which tells Formulog to treat them as part of the
extensional database (EDB).

```
@edb rel edge(node, node)
```

Formulog assumes that every relation not annotated with `@edb` is an intensional
database (IDB) relation, meaning that it is defined by rules and should be
treated as an output of the program. For instance, this predicate computes
transitive closure over the previously defined `edge` predicate:

```
rel tc(node, node)
tc(X, Y) :- edge(X, Y).
tc(X, Z) :- tc(X, Y), edge(Y, Z).
```

A Formulog rule consists of a list of head atoms (the atoms to the left of the
`:-`) and a list of body atoms (the atoms to the right of the `:-`). An atom is
either a nullary predicate symbol (i.e., a predicate that takes no arguments) or
a n-ary predicate symbol followed by a parenthesized, comma-separated list of
terms. Each term is either

* a primitive like `42`;
* a variable like `X`;
* a constructed term like `some(X :: [2, 3])`;
* a term of the form `t not C`, where `t` is a term and `C` is a constructor
  symbol (this evaluates to `true` if the outermost constructor of `t` is not
  `C`); or
* a function call to a user-defined or built-in function like `i32_to_i64(42)`
  (functions are described in the next section).

Additionally, atoms in the body of a rule can be negated, as in the atom `!tc(X,
"c")`. Restrictions on the use of negation will be described later in this
guide.

Formulog also has two built-in binary predicates, `=` and `!=`:

```
rel ok
ok :- X = "hello", X != "goodbye".
```

The first of these predicate is true when its arguments unify to the same term,
and the second is true when its arguments cannot be unified.

Finally, any Formulog term of type `bool` can be used in place of an atom in the
rule body, as here:

```
rel foo(bool)
output p
p :- foo(X), X.
```

where the rule is translated to

```
p :- foo(X), X = true.
```

### Reading EDB Relations from Disk

It is possible to specify that an EDB relation should be read from an external
file by annotating its declaration with `@disk`, as in

```
@disk @edb foo(i32, i32, string list)

@disk @edb bar(string)
```

The Formulog runtime will look in the directories specified on the command line
for files called`foo.tsv` and `bar.tsv` (defaulting to the current directory).
As suggested by the `.tsv` extension, these files should contain rows of
tab-separated terms, where each row corresponds to one input fact, and each
column corresponds to an argument position.

So, a file `foo.tsv` might look like this

```
42	0	["x"]
24	1	["", " "]
100	-1	[]
```

(note that the terms on a line are separated by tabs, *not* spaces); it would
correspond to the facts

```
foo(42, 0, ["x"]).
foo(24, 1, ["", " "]).
foo(100, -1, []).
```

Similarly, a `bar.tsv` file looking like this

```
"hello"
"goodbye"
"ciao"
"aloha"
```

would correspond to the facts

```
bar("hello").
bar("goodbye").
bar("ciao").
bar("aloha").
```

Every fact directory must have a `.tsv` file for _every_ external input
relation (the file can be empty).

### Writing IDB Relations to Disk

An IDB relation can be annotated with the annotation `@disk`, in which case
Formulog will dump its contents into a `.tsv` file in the directory specified on
the command line (defaulting to the current directory).

For example, the program

```
rel bar(i32, i32)
bar(1, 2).
bar(3, 4).

@disk rel foo(i32, i32)
foo(X, Y) :- bar(X, Y).
```

will result in a file `foo.tsv` with the tab-separated contents:

```
1	2
3	4
```

## Functions

Formulog allows users to define ML-style functions, that can then be invoked
from within Datalog-style rules. These functions can be polymorphic, but cannot
be higher-order. The functions must have explicit type annotations. For example,
here is a function for finding the nth element of a list:

```
fun nth(Xs : 'a list, N : i32) : 'a option =
  match Xs with
  | [] => none
  | X :: Xs =>
    if N < 0 then none
    else if N = 0 then some(X)
    else nth(Xs, N - 1)
  end
```

No special syntax is required for defining recursive functions, although
mutually recursive functions must be defined with `and`, as here:

```
fun neg_abs(X: i32) = if X > 0 then -X else X

fun is_even(X: i32) : bool =
  let X = neg_abs(X) in 
  X = 0 || is_odd(X + 1)
and is_odd(X: i32) : bool =
  let X = neg_abs(X) in
  X != 0 && is_even(X + 1)
```

We support some of the basic ML syntax constructions, like `match` and `let`.
However, you will find Formulog's syntax to be less flexible than most ML
implementations; for example, `some(X)` is okay but `some X` is not.

Despite the fact that we do not support higher-order functions, we do support
nested functions that can locally capture variables and we also support a
special parameterized term `fold`:

```
fold[f] : ['a, 'b list] -> 'a
```

where `f` is the name of a function of type `['a, 'b] -> 'a`. Here's an example
using both nested functions and `fold`:

```
fun rev(Xs: 'a list) : 'a list =
  let fun cons_wrapper(Xs: 'a list, X: 'a) : 'a list = X :: Xs in
  fold[cons_wrapper]([], Xs)
```

Top-level nullary functions (i.e., ones that take no arguments) can be
introduced with the keyword `const` instead of `fun`:

```
const pi : fp64 = 3.14
(* same as `fun pi : fp64 = 3.14` *)
```

### Lifted Relations and Aggregation

Formulog allows any relation (i.e., EDB relations, IDB relations, and the
built-in relations `!=` and `=`) to be lifted to a boolean-returning function.
For instance, we can write code like this:

```
output bar(i32)

fun foo(N:i32) : bool = bar(N + 1)
```

Here, the function `foo(n)` returns `true` whenever the `bar` relation contains
`n + 1`.

Formulog supports aggregation through the wild card term `??`, which can be used
as an argument when "invoking" a relation as a function. For example, given the
relation `p` that relates a `bool` to an `i32`, we have:

* `p(true, 42)` returns a boolean (whether `true` is related to `42`)
* `p(true, ??)` returns a list of `i32` terms (the ones that are related
  to `true`)
* `p(??, 42)` returns a list of `bool` terms (the ones that are related to `42`)
* `p(??, ??)` returns a list of pairs constituting the relation

The use of lifted predicates must be stratified, as described in the "Program
Safety" document.

### Built-in Functions

Finally, Formulog already has a bunch of basic functions built-in (mostly to do
with manipulating primitives):

* functions for basic mathematical operations for types `i32`, `i64`, `fp32`,
  and `fp64`:
    * addition (`*_add`), as in `fp32_add`
    * subtraction (`*_sub`)
    * multiplication (`*_mul`)
    * negation (`*_neg`)
* bit vector operations for types `i32` and `i64`:
    * bitwise and (`*_and`),
    * bitwise or (`*_or`)
    * bitwise exclusive or (`*_xor`), for types `i32` and `i64`;
    * signed division (`*_sdiv`)
    * signed remainder (`*_srem`)
    * unsigned division (`*_udiv`)
    * unsigned remainder (`*_urem`)
    * shift left (`*_shl`)
    * logical shift right (`*_lshr`)
    * arithmetic shift right (`*_ashr`)
* float operations for types `fp32` and `fp64`:
    * equality (`*_eq`; this is floating point equality, as opposed to
      structural equality via the predicate `=`);
    * division (`*_div`)
    * remainder (`*_rem`)
* Comparison operations `*_lt`, `*_le`, `*_gt`, `*_ge` for types `i32`, `i64`,
  `fp32`, and `fp64` (the bit vector ones are implicitly for signed comparison)
* Signed compare (`*_scmp`) and unsigned compare (`*_ucmp`) operators for types
  `i32` and `i64`; these return a term of type `cmp` (described above)
* boolean operators `!`, `&&`, and `||`
* numeric primitive conversion operations, in the form `*_to_*` (e.g.,
  `i32_to_fp64`)
* the operators `string_to_i32` and `string_to_i64`, which convert the string
  representation of an integer to a term of type `i32 option` and `i64 option`,
  respectively. The string should either be a decimal integer preceded
  optionally by `-` or `+`, or a hexadecimal integer preceded by `0x`. The
  operations return `none` if the string is not in the proper format or
  represents an integer too large to fit in 32/64 bits.

Standard arithmetic notation can be used for signed `i32` operations. For
example, `38 + 12 / 3` is shorthand for `i32_add(38, i32_sdiv(12, 3))`.

Formulog supplies some `string` manipulation functions:

```
string_concat      : [string, string] -> string
string_cmp         : [string, string] -> cmp
string_matches     : [string, string] -> bool
string_starts_with : [string, string] -> bool
substring          : [string, i32, i32] -> string option
string_length      : [string] -> i32
char_at            : [string] -> i32 option
string_to_list     : [string] -> i32 list
list_to_string     : [i32 list] -> string
to_string          : 'a -> string
```

The function `string_matches` returns `true` when its first argument matches its
second argument, which can be a regular expression. The function
`string_starts_with` returns `true` when its second argument is a prefix of its
first argument. The function `substring(s, i, j)` extracts the substring of `s`
starting at index `i` and ending at index `j - 1`; it returns `none` for
inappropriate `i` or `j`.

The functions `char_at`, `string_to_list`, and `list_to_string` can be used to
treat a string as a list of characters. We represent characters as terms of
type `i32`. We currently do not guarantee any particular behavior if an integer
less than 0 or greater than 255 is used as a character.

Finally, for the purposes of debugging, Formulog supplies a `print` function of
type `'a -> bool`; it always evaluates to `true`.
