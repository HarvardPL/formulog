---
title: Eager Evaluation
layout: page
parent: Evaluation Modes
nav_order: 4
---

# Eager Evaluation

In addition to traditional semi-naive Datalog evaluation, Formulog supports _eager evaluation_, a novel concurrent evaluation algorithm for Datalog that is faster than semi-naive evaluation on some Formulog workloads (often because it induces a more favorable distribution of the SMT workload across SMT solvers).
Whereas semi-naive evaluation batches derived tuples to process them in explicit rounds, eager evaluation eagerly pursues the consequences of each tuple as it is derived.

Using eager evaluation with the Formulog interpreter is easy: just add the `--eager-eval` flag.
Eager evaluation can also be used with the Formulog compiler, provided you install [our custom version of Souffle](https://github.com/aaronbembenek/souffle).
When you configure `cmake` on the generated code, you need to add `-DFLG_EAGER_EVAL=On`.
For example, to build a version of the greeting program that uses eager evaluation, use these commands:

```
java -jar formulog.jar -c examples/greeting.flg && \
  cd codegen && \
  cmake -B build -S . -DCMAKE_BUILD_TYPE=Release -DFLG_EAGER_EVAL=On && \
  cmake --build build -j && \
  ./build/flg --dump-idb
```

For more information about eager evaluation, see the OOPSLA'24 paper [Making Formulog Fast: An Argument for Unconventional Datalog Evaluation](https://dl.acm.org/doi/10.1145/3689754) by Aaron Bembenek, Michael Greenberg, and Stephen Chong.