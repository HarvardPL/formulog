# Formulog

![Build Status](https://github.com/HarvardPL/formulog/actions/workflows/maven.yml/badge.svg)

**TL;DR: write SMT-based program analyses (symbolic executors, refinement type checkers, etc.) in an optimized Datalog-like language.**

Datalog has proven to be a useful language for implementing a range of program analyses, but analyses that use SMT solving cannot be easily written in traditional versions of Datalog.
Formulog sets out to fill this gap by augmenting Datalog with ways to construct and reason about SMT formulas, as well as some first-order functional programming to make life easier.

**Why write your SMT-based analysis in Formulog?**

1. By combining logic programming, functional programming, and SMT solving, Formulog makes it possible to encode many analyses declaratively at the level of mathematical specification (e.g., inference rules), closing the gap between specification and implementation---and often revealing bugs in the spec!
2. This high-level encoding makes it possible for Formulog to apply high-level optimizations to your analysis, like automatic parallelization and goal-directed evaluation.
3. Thanks to our [Formulog-to-Soufflé compiler](https://harvardpl.github.io/formulog/eval_modes/compile.html), you can automatically generate a C++ version of the analysis that leverages highly optimized Datalog algorithms and data structures.

**Interested?**
For more information, check out the [Formulog docs](https://harvardpl.github.io/formulog/) (also available in the [docs](./docs/) directory), including [tips on getting started](https://harvardpl.github.io/formulog/starting.html) and the [language reference](https://harvardpl.github.io/formulog/lang_ref/).
To get a sense for what's involved in building a nontrivial SMT-based analysis in Formulog,
check out our [tutorial](https://harvardpl.github.io/formulog/tutorial/) on implementing a refinement type checker in Formulog.

## Contributing

Contributions to this project are most welcome!
Please open a [GitHub issue](https://github.com/HarvardPL/formulog/issues/new) and then link a pull request to it.
Pull requests must be in the [Google Java format](https://github.com/google/google-java-format) before being merged.
To reformat your code, run `mvn spotless:apply`; you can also check if your code is conformant (without reformatting it) by running `mvn spotless:check`.

## Licensing and Third-Party Libraries

Formulog is released under an [Apache 2.0 license](./LICENSE.txt).

This project uses third-party libraries. You can generate a list of these
libraries and download their associated licenses with this command:

```
mvn license:download-licenses
```

The generated content can be found in the `target/generated-resources/`
directory.
