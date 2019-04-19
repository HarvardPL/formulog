# FormuLog 
Datalog with support for SMT queries.

## Setup

NB: All these instructions are for Linux. Hopefully they translate to other platforms :)

Dependencies:

* Maven
* JDK 1.8+
* Z3 (in particular, you need to have the `z3` binary on your path)

To build an executable JAR, run the command `mvn package` from the project
directory. This will create a JAR called
`formulog-0.0.1-SNAPSHOT-jar-with-dependencies.jar` in the `target/`
directory. When invoked as an executable JAR, this program expects a single
FormuLog file as an argument.

For instance, if you run this command from the main repo directory, you should
see the result `ok`:

```
java -jar target/formulog-0.0.1-SNAPSHOT-jar-with-dependencies.jar src/test/resources/test040_ok.flg
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
java -jar -DdebugSmt target/formulog-0.0.1-SNAPSHOT-jar-with-dependencies.jar src/test/resources/test040_ok.flg
```

## Use

See the wiki for the GitHub repo for FormuLog documentation. There's a Vim
syntax file in the `misc/` directory.

## Third-party libraries

This project uses third-party libraries. You can generate a list of these
libraries and download their associated licenses with this command:

```
mvn license:download-licenses
```

The generated content can be found in the `target/generated-resources/` directory.
