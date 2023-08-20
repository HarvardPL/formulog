# Formulog

![Build Status](https://github.com/HarvardPL/formulog/actions/workflows/maven.yml/badge.svg)]

Datalog with support for SMT queries and first-order functional programming.

## Setup

### Prepackaged JAR

You can find a prepackaged JAR file in the Releases section of the GitHub
repository.

Dependencies:

* JRE 11+
* A supported SMT solver (see discussion below)

### Docker

Prebuilt images are available
on [Docker Hub](https://hub.docker.com/r/aaronbembenek/formulog). If you have
Docker installed, you can spin up an Ubuntu container with Formulog and some
example programs by running this command:

```bash
docker run -it aaronbembenek/formulog:0.7.0 # may require sudo
```

This should place you in the directory `/root/formulog/`. From here, you should
be able to run the following command and see some greetings:

```bash
java -jar formulog.jar examples/greeting.flg --dump-idb
```

### Building from source

Dependencies:

* JDK 11+
* Maven
* A supported SMT solver (see discussion below)

To build an executable JAR, run the command `mvn package` from the project
directory. This will create an executable JAR with a name like
`formulog-X.Y.Z-SNAPSHOT-jar-with-dependencies.jar` in the `target/`
directory.

If `mvn package` fails during testing, it might mean that there is a problem
connecting with your SMT solver. You can compile without testing by adding the
`-DskipTests` flag.

### Supported SMT solvers

We have primarily used Formulog with Z3 as the backend solver. Z3's textual
interface can change even between patch versions. Z3 4.11.1 is known to work
with Formulog. To use Z3, the binary `z3` must be on your path.

We also have some experimental (not recently tested) support for other solvers;
not all these solvers handle the full range of Formulog features. To use a
solver besides Z3, you need to set the `smtSolver` system property (see below).
For each solver, the relevant binary needs to be on your path: `z3` for
Z3, `boolector` for Boolector, `cvc4` for CVC4, and `yices-smt2` for Yices.

### Zenodo artifact (OOPSLA'20 paper)

[![Zenodo DOI 10.5281/zenodo.4039085](https://zenodo.org/badge/DOI/10.5281/zenodo.4039085.svg)](https://doi.org/10.5281/zenodo.4039085)

You can replicate our evaluation from
the [OOPSLA'20 paper](https://dl.acm.org/doi/10.1145/3428209) following
the [instructions on Zenodo](https://zenodo.org/record/4039085). To start,
[download the Docker image tarball](https://zenodo.org/record/4039085/files/formulog-artifact-image.tar.gz?download=1)
for the artifact and load it using Docker:

```ShellSession
$ curl "https://zenodo.org/record/4039085/files/formulog-artifact-image.tar.gz?download=1" -o formulog-artifact-image.tar.gz
$ docker load < formulog-artifact-image.tar.gz # may require sudo
$ docker run -it formulog-artifact             # may require sudo
```

## Running Formulog

The executable Formulog JAR that you have either downloaded or built expects a
single Formulog file as an argument.

For example, if you save this Formulog program to `greeting.flg`

```
@edb rel entity(string)
entity("Alice").
entity("Bob").
entity("World").

rel greeting(string)
greeting(Y) :-
  entity(X),
  some(M) = get_model([`#y[string] #= str_concat("Hello, ", X)`], none),
  some(Y) = query_model(#y[string], M).
```

and run the command

```
java -jar formulog.jar greeting.flg --dump-idb
```

(assuming `formulog.jar` is the name of the Formulog executable JAR), you should see results like the following:

```
Parsing...
Finished parsing (0.202s)
Type checking...
Finished type checking (0.024s)
Rewriting and validating...
Finished rewriting and validating (0.253s)
Evaluating...
Finished evaluating (0.354s)

==================== SELECTED IDB RELATIONS ====================

---------- greeting (3) ----------
greeting("Hello, Alice")
greeting("Hello, Bob")
greeting("Hello, World")
```

### Options

The Formulog interpreter currently provides the following options:

```
Usage: formulog [-chV] [--dump-all] [--dump-idb] [--dump-query] [--dump-sizes]
                [--smt-stats] [--codegen-dir=<codegenDir>] [-D=<outDir>]
                [-j=<parallelism>] [--smt-solver-mode=<smtStrategy>]
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

**Note:** The interpreter does not print any results by default; use one of the
`--dump*` options to print results to the console, or annotate intensional
database (IDB) relations with `@disk` to dump them to disk.

### System properties

In addition to options, there are many system properties that can be set using
the `-D` flag (as in `-DdebugSmt` or `-DuseDemandTransformation=false`). Most of
the properties are not yet documented; many are defined in the
class `edu.harvard.seas.pl.formulog.Configuration`; some of the most useful ones
are:

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

For example, to run the test program above with SMT debug information and 3
threads, use

```
java -DdebugSmt -jar formulog.jar greeting.flg -j 3
```

## Compiling Formulog programs

As an alternative to being directly interpreted, Formulog programs can be compiled into a mix of C++ and Souffle code, which can then in turn be compiled into an efficient executable.
To enable compilation, set the `--codegen` (`-c`) flag; generated code will be placed in the directory `./codegen/` (you can change this using the `--codegen-dir` option).
Within this directory you can use `cmake` to compile the generated code into a binary named `flg`.

For example, to compile and execute the `greeting.flg` program from above, you can use these steps:

```shellsession
$ java -jar formulog.jar -c greeting.flg
$ cd codegen
$ cmake -B build -S .
$ cmake --build build -j
$ ./build/flg --dump-idb
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

### Dependencies

To build the generated code, you must have:

- A C++ compiler that supports the C++17 standard (and OpenMP, if you want to produce a parallelized binary)
- `cmake` (v3.21+)
- [`boost`](https://www.boost.org/) (a version compatible with v1.79)
- [`oneTBB`](https://oneapi-src.github.io/oneTBB/) (v2021.8.0 is known to work)
- [`souffle`](https://souffle-lang.github.io/) (v2.3 is known to work)

The Formulog Docker image already has these dependencies installed.

## Writing Formulog programs

See the documentation in `docs/`. Some shortish example programs can be found in
the `examples/` directory. To see an example of a larger development, check out
our implementation of
a [type checker for Dminor](https://github.com/HarvardPL/dminor-in-formulog), a
language built around refinement types.

There's a Vim syntax file in the `misc/` directory.

## Third-party libraries

This project uses third-party libraries. You can generate a list of these
libraries and download their associated licenses with this command:

```
mvn license:download-licenses
```

The generated content can be found in the `target/generated-resources/`
directory.
