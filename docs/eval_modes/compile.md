---
title: Compilation
layout: page
parent: Evaluation Modes
nav_order: 3
---

# Compilation

As an alternative to being directly interpreted (the default), Formulog programs can be compiled into a mix of C++ and Souffle code, which can then in turn be compiled into an efficient executable.
To enable compilation, set the `--codegen` (`-c`) flag; generated code will be placed in the directory `./codegen/` (you can change this using the `--codegen-dir` option).
Within this directory you can use `cmake` to compile the generated code into a binary named `flg`.

For example, to compile and execute the `greeting.flg` program from above, you can use these steps:

```
java -jar formulog.jar -c examples/greeting.flg && \
  cd codegen && \
  cmake -B build -S . -DCMAKE_BUILD_TYPE=Release && \
  cmake --build build -j && \
  ./build/flg --dump-idb
```

This should produce output like the following:

```
Parsing...
Finished parsing (0.000s)
Evaluating...
Finished evaluating (0.029s)

==================== SELECTED IDB RELATIONS ====================

---------- greeting (3) ----------
greeting("Hello, Bob")
greeting("Hello, World")
greeting("Hello, Alice")
```

Use the command `./build/flg -h` see options available when running the executable.

For more information about the Formulog compiler, see the OOPSLA'24 paper [Making Formulog Fast: An Argument for Unconventional Datalog Evaluation](https://dl.acm.org/doi/10.1145/3689754) by Aaron Bembenek, Michael Greenberg, and Stephen Chong.

## Dependencies

To build the generated code, you must have:

- A C++ compiler that supports the C++17 standard (and OpenMP, if you want to produce a parallelized binary)
- `cmake` (v3.21+)
- [`boost`](https://www.boost.org/) (a version compatible with v1.81)
- [`oneTBB`](https://oneapi-src.github.io/oneTBB/) (v2021.8.0 is known to work)
- [`souffle`](https://souffle-lang.github.io/) (v2.3 is known to work; you have to use our [custom fork](https://github.com/aaronbembenek/souffle) if you want to combine compilation with [eager evaluation]({{ site.base_url }}{% link eval_modes/eager.md %}).)

The Formulog Docker image already has these dependencies installed.