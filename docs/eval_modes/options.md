---
title: Options and System Properties 
layout: page
parent: Evaluation Modes
nav_order: 1
---

# Options and System Properties 

Formulog evaluation is controlled by options and system properties.
For example, to interpret the test program with SMT logging and 2
threads, use the `debugSmt` property and `-j 2` option:

```
java -DdebugSmt -jar formulog.jar example/greeting.flg -j 2
```

## Options

Run Formulog with the `-h` flag to see a list of the command-line options that are currently available.
As of Formulog v0.8.0, they are:

```
Usage: formulog [-chV] [--dump-all] [--dump-idb] [--dump-query] [--dump-sizes]
                [--eager-eval] [--smt-stats] [--codegen-dir=<codegenDir>]
                [-D=<outDir>] [-j=<parallelism>]
                [--smt-solver-mode=<smtStrategy>]
                [--dump=<relationsToPrint>]... [-F=<factDirs>]... <file>
Runs Formulog.
      <file>         Formulog program file.
  -c, --codegen      Compile the Formulog program.
      --codegen-dir=<codegenDir>
                     Directory for generated code (default: './codegen').
  -D, --output-dir=<outDir>
                     Directory for .tsv output files (default: '.').
      --dump=<relationsToPrint>
                     Print selected relations.
      --dump-all     Print all relations.
      --dump-idb     Print all IDB relations.
      --dump-query   Print query result.
      --dump-sizes   Print relation sizes.
      --eager-eval   Use eager evaluation (instead of traditional semi-naive
                       Datalog evaluation)
  -F, --fact-dir=<factDirs>
                     Directory to look for fact .tsv files (default: '.').
  -h, --help         Show this help message and exit.
  -j, --parallelism=<parallelism>
                     Number of threads to use.
      --smt-solver-mode=<smtStrategy>
                     Strategy to use when interacting with external SMT solvers
                       ('naive', 'push-pop', or 'check-sat-assuming').
      --smt-stats    Report basic statistics related to SMT solver usage.
  -V, --version      Print version information and exit.
```

**Note:** Formulog does not print any results by default; use one of the
`--dump*` options to print results to the console, or annotate intensional
database (IDB) relations with `@disk` to dump them to disk.

## System Properties

In addition to options, there are many system properties that can be set using
the `-D` flag (as in `-DdebugSmt` or `-DuseDemandTransformation=false`). Some of
the most useful ones are:

* `debugSmt` - log debugging information related to SMT calls to
  the `solver_logs/` directory (defaults to false)
* `debugMst` - print debugging information related to the magic set
  transformation (defaults to false)
* `debugRounds` - print statistics for each round of seminaive evaluation
  (defaults to false)
* `useDemandTransformation` - apply the demand transformation as a
  post-processing step after the magic set transformation (defaults to true)
* `softExceptions` - ignore exceptions during evaluation (i.e., treat them as
  unification failures, and not as something that should stop evaluation;
  defaults to false)
* `sequential` - run interpreter without a thread pool (helpful for debugging
  runtime; defaults to false)
* `printRelSizes` - print final relation sizes (defaults to false)
* `printFinalRules` - print the final, transformed rules (defaults to false)
* `trackedRelations=REL_1,...,REL_n` - print facts from listed relations as they
  are derived (defaults to the empty list)
* `smtLogic=LOGIC` - set the logic used by the external SMT solver (defaults to
  `ALL`)
* `smtSolver=SOLVER` - set the external SMT solver to use; current options are
  `z3` (default), `cvc4`, `yices`, and `boolector`
* `smtDeclareAdts` - whether to declare Formulog algebraic data types to the SMT
  solver upon initialization; set this to false for logics that do not support
  ADTs (defaults to true)

### Alternative SMT Solvers

While we have primarily used Formulog with Z3 as the backend solver, we also
have some experimental (not recently tested) support for other solvers; not all
these solvers handle the full range of Formulog features. To use a solver
besides Z3, you need to set the `smtSolver` system property (see above).  For
each solver, the relevant binary needs to be on your path: `z3` for Z3,
`boolector` for Boolector, `cvc4` for CVC4, and `yices-smt2` for Yices.