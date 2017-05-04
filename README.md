Slicer
======

[![Build Status](https://travis-ci.org/jstolarek/slicer.svg?branch=master)](https://travis-ci.org/jstolarek/slicer)

Slicer is an interpreter for a simple ML-like language called iTML (imperative
Transparent ML).  This is companion code for paper "Imperative Functional
Programs that Explain their Work" by Wilmer Ricciotti,
[Jan Stolarek](http://ics.p.lodz.pl/~stolarek),
[Roly Perera](http://www.dcs.gla.ac.uk/~roly/) and
[James Cheney](http://homepages.inf.ed.ac.uk/jcheney/), published at
[International Conference on Functional Programming 2017](http://icfp17.sigplan.org).


Requirements
============

This software is written in Haskell.  To build and install it you will need GHC
8.0 or newer and a typical Haskell infrastructure (Cabal, access to Hackage).


Installation
============

1. Get the sources:

   ```
   git clone https://github.com/jstolarek/slicer
   ```

2. Initialize cabal sandbox (optional, but recommended):

   ```
   cd slicer
   cabal sandbox init
   ```

3. Install dependencies:

   ```
   cabal install --dependencies-only
   ```

   If you want to run tests or benchmarks add `--enable-tests` or
   `--enable-benchmarks` respectively to the above command.

4. Configure and build the project

   ```
   cabal configure
   cabal build
   ```


Usage
=====

After following the above steps the slicer executable will be located at
`dist/build/slicer/slicer`.  Example TML programs are located in `examples`
sub-directory.  You can run them by passing file name on the command line:

```
$ ./dist/build/slicer/slicer examples/icfp17-example.tml
```

If all went well you should see the output:

```
Running examples/icfp17-example.tml
val it = let f = (fun f x =>
         if x == 0
         then y := 6 * !z
         else _) in
try
  f 0
with _ =>
  _
;; !y : trace(int)
```

You can pass more than one file name at the same time.

REPL
----

Slicer provides a very simple REPL.  Invoke it by passing `--repl` flag:

```
$ ./dist/build/slicer/slicer --repl
Welcome to Slicer REPL
slicer>
```

You can interact with REPL by providing single-line declarations:

```
slicer> data intlist = Nil | Cons int * intlist
slicer> let tail = fun tail (xs : intlist) : intlist => case xs of Nil -> Nil; Cons xs' -> snd xs'
val it = (fun tail xs =>
 case xs of
   Nil -> Nil;
   Cons xs' -> snd xs') : (intlist -> intlist)
slicer> let t = trace (tail (Cons (1, Cons (2, Cons (3, Nil)))))
val it = trace (tail Cons (1, Cons (2, Cons (3, Nil)))) : trace(intlist)
slicer> bwdSlice (t, Cons (2, _:intlist))
val it = tail Cons (_, Cons (2, _)) : trace(intlist)
```


Running the test suite
----------------------

All example programs are packaged into a single test suite.  Build and run the
testsuite with:

```
cabal install --dependencies-only --enable-tests
cabal build
cabal test
```

The test suite will run every program in `examples` directory and compare its
output with the expected output stored in a corresponding `*.golden` file inside
`tests/golden-templates/`.


Source code tour
================

Source code is divided into a library and an executable that depends on the
library.  The library is located in `lib` directory.  Under
`lib/Language/Slicer/ you will find these modules:

  * `Absyn`: abstract syntax for TML language.  This is what the parser
    produces (`Parser` module).

  * `Core`: abstract syntax tree for the core language.  Produced from TML
    abstract syntax tree (`Absyn` module) during desugaring (`Desugar` module).
    Contains also built-in operators and functions for working with the store
    abstraction.

  * `Desugar` - translates TML abstract syntax tree (`Absyn` module) into core
    language (`Core` module).

  * `Env` - definitions of variable and type environments + helper functions.

  * `Error` - data type for handling compilation errors.

  * `Eval` - evaluation of core programs

  * `Monad` module and `Monad/` sub-directory - monads for running various
    stages of the interpreter pipeline.

  * `Parser` - well, the parser.

  * `Primitives` - built-in language primitives

  * `Resugar` - translate core programs into surface-like syntax.  Used for
    pretty-printing.

  * `Run` - entry points to the interpreter

  * `Slice` - implementation of slicing

  * `UpperSemiLattice` - lattice definition


Executable is located inside `src` directory.  `src/Language/Slicer/` contains:

  * `Main` - executable logic (parsing command line options, invoking the
    library, etc.)

  * `Monad/` - REPL monad

  * `Repl` - REPL logic


Disclaimer
==========

This is experimental research software.  It comes as-is without any guarantees.
