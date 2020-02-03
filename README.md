# Formulog 
Datalog with support for SMT queries.

## Setup

Dependencies:

* JRE 1.8+
* The SMT solver Z3 (in particular, you need to have the `z3` binary on your
  path)

### Prepackaged JAR

You can find a prepackaged JAR file in the Releases section of the GitHub
repository.

### Building from source

Additional dependencies:

* JDK 1.8+
* Maven

To build an executable JAR, run the command `mvn package` from the project
directory. This will create an executable JAR with a name like 
`formulog-X.Y.Z-SNAPSHOT-jar-with-dependencies.jar` in the `target/`
directory.

If `mvn package` hangs during testing, it likely means that something is wrong
with Z3. You can compile without testing by adding the `-DskipTests` flag.

## Running Formulog

The executable Formulog JAR that you have either downloaded or built expects a
single Formulog file as an argument.

For example, if you save this Formulog program to `greeting.flg`

```
input entity(string)
entity("Alice").
entity("Bob").
entity("World").

output greeting(string)
greeting(Y) :-
  entity(X),
  some(M) = get_model(`#y[string] #= str_concat("Hello, ", X)`, none),
  some(Y) = query_model(#y[string], M).
```

and run the command

```
java -jar formulog.jar greeting.flg 
```

(assuming `formulog.jar` is the name of the Formulog executable JAR), you
should see the results:

```
entity("Alice")
entity("Bob")
entity("World")
greeting("Hello, Alice")
greeting("Hello, Bob")
greeting("Hello, World")
```

### Options

You can set the following system properties (using the `-D` flag, as in
`-DdebugSmt` or `-DuseDemandTransformation=false`):

* `debugSmt` - print debugging information related to SMT calls (defaults to
  false)
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
* `parallelism=N` - run interpreter with `N` threads (defaults to 4)
* `printRelSizes` - print final relation sizes (defaults to false)
* `printFinalRules` - print the final, transformed rules (defaults to false)
* `factDirs=dir_1,...,dir_n` - directories for CSV files of input facts
  (defaults to the current directory)
* `trackedRelations=rel_1,...,rel_n` - print facts from listed relations as
  they are derived (defaults to the empty list)
* `printResults=(all|none|edb|idb|query|some=rel_1,...,rel_n)` - restrict which
  types of facts are printed after evaluation (default is all)

For example, to run the test program above with SMT debug information and 3
threads, use

```
java -DdebugSmt -Dparallelism=3 -jar formulog.jar greeting.flg
```

## Writing Formulog programs

See the documentation in `docs/`. Some shortish example programs can be found
in the `examples/` directory. To see an example of a larger development, check
out our implementation of a [type checker for
Dminor](https://github.com/HarvardPL/dminor-in-formulog), a language built
around refinement types.

There's a Vim syntax file in the `misc/` directory.

## Third-party libraries

This project uses third-party libraries. You can generate a list of these
libraries and download their associated licenses with this command:

```
mvn license:download-licenses
```

The generated content can be found in the `target/generated-resources/`
directory.
