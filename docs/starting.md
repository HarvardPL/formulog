---
title: Getting Started
layout: page
nav_order: 2
---

# Getting Started

Thank you for your interest in Formulog!
This page describes how to install Formulog and provides some pointers on writing Formulog programs.

## Seting up Formulog

There are three main ways to set up Formulog (listed in increasing order of number of dependencies):

- Using the Docker image
- Downloading the JAR
- Building from source

### Use the Docker image

Prebuilt images are available on [Docker Hub](https://hub.docker.com/r/aaronbembenek/formulog).
If you have Docker installed, you can spin up an Ubuntu container with Formulog, our custom version of Soufflé, and some example programs by running this command (replace `X.Y.Z` with the latest version):

```bash
docker run -it aaronbembenek/formulog:X.Y.Z # may require sudo
```

This should place you in the directory `/root/formulog/`, with a file `formulog.jar` and some example Formulog programs in the `examples/` directory.

### Download the JAR

Dependencies:

- JRE 11+
- Z3 (v4.12.2 is known to work; other recent versions should work too)

You can find a prepackaged JAR file in the [Releases section](https://github.com/HarvardPL/formulog/releases) of the GitHub repository.

### Build from Source

Dependencies:

- JDK 11+
- Maven (v3.9.5 is known to work)
- Z3 (v4.12.2 is known to work; other recent versions should work too)

To build an executable JAR, run the command `mvn package` from the project source directory.
This will create an executable JAR with a name like `formulog-X.Y.Z-SNAPSHOT-jar-with-dependencies.jar` in the `target/` directory.

If `mvn package` fails during testing, it might mean that there is a problem connecting with Z3.
You can compile without testing by adding the `-DskipTests` flag.

### Test Your Setup

If you have set up Formulog, you should now have an executable JAR at your fingertips.
The JAR expects a single Formulog file as an argument.
Let's test it on the following Formulog program (available in the Docker image and the base repository directory as `examples/greeting.flg`):

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

Run the following command (where `formulog.jar` is replaced with the name of the executable JAR):

```
java -jar formulog.jar examples/greeting.flg --dump-idb
```

You should get results like these, indicating that three `greeting` facts have been derived:

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

## Writing Formulog Programs

Now that you have Formulog set up, the fun part starts: writing Formulog programs!

Check out our [tutorial]({{ site.baseurl }}{% link tutorial/index.md %}) for a walk-through of how to encode a refinement type system in Formulog.
Additional short-ish example programs can be found in the `examples/` directory (in the Docker image or repository base directory).
For examples of larger developments, see the case studies we have used in publications:

- [a refinement type checker](https://github.com/aaronbembenek/making-formulog-fast/blob/main/benchmarks/dminor/bench.flg)
- [a bottom-up points-to analysis for Java](https://github.com/aaronbembenek/making-formulog-fast/blob/main/benchmarks/scuba/bench.flg)
- [a symbolic executor an LLVM fragment](https://github.com/aaronbembenek/making-formulog-fast/blob/main/benchmarks/symex/bench.flg)

See the [language reference]({{ site.baseurl }}{% link lang_ref/index.md %}) for details about Formulog constructs.

Syntax highlighting is available for Visual Studio Code (follow instructions [here](https://github.com/HarvardPL/formulog-syntax)) and Vim (install [misc/flg.vim](https://github.com/HarvardPL/formulog/blob/master/misc/flg.vim)).

Finally, please raise a [GitHub issue](https://github.com/HarvardPL/formulog/issues/new) if you want to try out Formulog but would like additional information or assistance---we're happy to help! :)
