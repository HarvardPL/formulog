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
directory. This will create an executable JAR called
`formulog-0.0.1-SNAPSHOT-jar-with-dependencies.jar` in the `target/`
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

Use the option `-v` for verbose mode and `-j N` to run the evaluator with a
thread pool of size `N` (defaults to 1).

You can also set the following system properties (using the `-D` flag, as in
`-DdebugSmt`):

* `debugSmt` - print debugging information related to SMT calls
* `debugMst` - print debugging information related to the magic set
  transformation
* `softExceptions` - ignore exceptions during evaluation (i.e., treat them as
  unification failures, and not as something that should stop evaluation)

For example, to run the test program above with SMT debug information, use

```
java -jar -DdebugSmt formulog.jar greeting.flg
```

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
