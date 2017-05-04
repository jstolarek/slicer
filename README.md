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
   cd slicer
   ```

2. If you want to work on the exact version that was submitted for the ICFP 2017
   artefact evaluation check out the relevant tag:

   ```
   git checkout icfp2017-final
   ```

3. Initialize cabal sandbox:

   ```
   cd slicer
   cabal sandbox init
   ```

4. Install dependencies:

   ```
   cabal install --dependencies-only
   ```

   If you want to run tests or benchmarks add `--enable-tests` or
   `--enable-benchmarks` respectively to the above command.

5. Configure and build the project

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


Reproducing examples from the paper
===================================

In the paper we have discussed several examples.  These are all located as
source files inside `examples/` directory.

1. On the first page of the paper we present a following example:

   ```ml
   let f(x) = if (x == 0) then y := 6 * !z else (y := 84 / !z; w := g(!y + 12))
   ```

   This example can be found in file `icfp17-example.tml`.  Run it with:

   ```
   $ ./dist/build/slicer/slicer examples/icfp17-example.tml
   ```

   You can tweak initial value of `z` and the value of argument passed to `f` to
   obtain different results.  Remember that you must change the slicing
   criterion to match the obtained result.  So for example if you change initial
   value of `z` to be `0` rather than `7` you need to change the slicing
   criterion from:

   ```ml
   bwdSlice ( t, 42 )
   ```

   to

   ```ml
   bwdSlice ( t, raise "Division by zero" )
   ```

2. On the third page of the paper we present a more elaborate example containing
   a usage of `map`.  This example can be found in `icfp17-example2.tml` source
   file.  Run it with:

   ```
   $ ./dist/build/slicer/slicer examples/icfp17-example2.tml
   ```

3. In section 6 we discuss an iTML program that solves a system of linear
   equations by using simple Gaussian elimination without pivoting.  This
   program can be found in `gauss.tml` source file (its pretty-printed version
   can be found in Appendix C in the extended version of the paper).  Run it
   with:

   ```
   $ ./dist/build/slicer/slicer examples/gauss.tml
   ```

   In this program we define two systems of equations.  System defined by arrays
   `as` and `bs` is solved correctly.  System defined by arrays `as'` and `bs'`
   causes a division by zero.  We then map `gauss` function over a list
   containing arrays defining both systems.  This allows us to demonstrate that
   our method works in a higher-order setting even for complex functions.  Note
   that we slice the program w.r.t. "Division by zero" exception.  That is
   because we know our program divides by zero and we want to understand why.
   After running the program observe the results:

     * all elements of arrays `as` and `bs` are replaced with holes.  This
       means that neither of them contributed to raising the exception.

     * some elements of `as'` are replaced with holes and some are not.  This
       means that some elements of that array contributed to raising the
       exception.  The last of the elements that was not replaced with a hole
       is located at row 2, column 1 (0-based indexing).  Knowing the nature of
       Gaussian elimination leads us to conclusion that this is where the
       division by zero must have taken place.

     * in the definition of `gauss` method code responsible for zeroing
       elements above the diagonal has been replaced by a hole.  This means
       that this code did not contribute to the result and so the exception was
       raised when zeroing elements below the diagonal.


Learning iTML
=============

Syntax iTML is based on ML.  Here are some basic information that should get you
started:

  * built-in primitive types are: `int`, `double`, `bool`, `string` and `unit`.

  * iTML does not support polymorphic types

  * you can define your own ADTs but iTML only allows them to have two
    constructors.  Moreover, constructors can only be nullary or unary.  So a
    list of integers would be defined as:

    ```ml
    data intlist = Nil | Cons (int * intlist)
    ```

    A standard `map` function defined over a list of integers (no polymorphism -
    remember!) looks like this:

    ```ml
    let map = fun map (f : int -> int) (xs : intlist) : intlist =>
       case xs of
          Nil -> Nil;
          Cons y -> Cons (f (fst y), map f (snd y))
    ```

    Note the calls to `fst` and `snd` - these are a consequence of storing head
    and tail of a list inside a tuple (`Cons` can be at most unary).

  * all data declarations should be placed before the program code

  * iTML does not support top-level bindings at the moment.  In other words,
    once you define data types the remaining program is just a single expression.

  * parser currently binds operators tighter than function application.  So for
    example `fst (raise "foo") + 2` is parsed as `fst ((raise "foo") + 2)`
    rather than `(fst (raise "foo")) + 2`.  Use parentheses to disambiguate.

  * enclose code inside a `trace` primitive to trace that code.  Use `bwdSlice`
    for backward slicing:

    ```ml
    let t = trace ( (* YOUR CODE HERE *) ) in
    bwdSlice (t, (* SLICING CRITERION HERE *) )
    ```

With all that in mind we recommend that you look at programs in `examples/`
directory.


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
