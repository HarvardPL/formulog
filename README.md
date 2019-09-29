# FormuLog 
Datalog with support for SMT queries.

## Setup

### Prepackaged JAR

You can find a prepackaged JAR file in the Releases section of the GitHub
repository. You will need to separately install the SMT solver Z3 so that the
executable `z3` is on your path.

### Building from source

Dependencies:

* Maven
* JDK 1.8+
* Z3 (in particular, you need to have the `z3` binary on your path)

To build an executable JAR, run the command `mvn package` from the project
directory. This will create an executable JAR with a name like 
`formulog-X.Y.Z-SNAPSHOT-jar-with-dependencies.jar` in the `target/`
directory.

## Running FormuLog

The executable FormuLog JAR that you have either downloaded or built expects a
single FormuLog file as an argument.

For example, if you save this FormuLog program to `greeting.flg`

```
input entity(string).
entity("Alice").
entity("Bob").
entity("World").

output greeting(string).
greeting(Y) :-
  entity(X),
  some(M) = get_model(`#y[string] #= str_concat("Hello, ", X)`, none),
  some(Y) = query_model(#y[string], M).
```

and run the command

```
java -jar formulog.jar greeting.flg 
```

(assuming `formulog.jar` is the name of the FormuLog executable JAR), you
should see the results:

```
entity("Alice").
entity("Bob").
entity("World").
greeting("Hello, Alice").
greeting("Hello, Bob").
greeting("Hello, World").
```

### Options

Use the option `-v` for verbose mode.

You can also set the following system properties (using the `-D` flag, as in
`-DdebugSmt` or `DuseDemandTransformation=false`):

* `callTrace` - print debugging information related to FormuLog-level function
  calls (defaults to false)
* `debugSmt` - print debugging information related to SMT calls (defaults to
  false)
* `debugMst` - print debugging information related to the magic set
  transformation (defaults to false)
* `useDemandTransformation` - apply the demand transformation as a
  post-processing step after the magic set transformation (defaults to true)
* `softExceptions` - ignore exceptions during evaluation (i.e., treat them as
  unification failures, and not as something that should stop evaluation;
  defaults to false)
* `sequential` - run interpreter without a thread pool (helpful for debugging
  runtime; defaults to false)
* `parallelism=N` - run interpreter with `N` threads (defaults to 4)

For example, to run the test program above with SMT debug information, use

```
java -DdebugSmt -jar formulog.jar greeting.flg
```

### Disclaimer

We have not yet focused on the performance or scalability of the FormuLog
runtime. We hope to improve it soon (most likely by integrating the language
features of FormuLog into an existing Datalog implementation). Stay tuned!

## Writing FormuLog programs

See the wiki on the GitHub repo for FormuLog documentation. 

There's a Vim syntax file in the `misc/` directory.

## Third-party libraries

This project uses third-party libraries. You can generate a list of these
libraries and download their associated licenses with this command:

```
mvn license:download-licenses
```

The generated content can be found in the `target/generated-resources/` directory.
