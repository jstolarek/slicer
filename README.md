Slicer
======

Slicer is an interpreter for a simple ML-like language called iTML (imperative
Transparent ML).  This is companion code for paper "Imperative Functional
Programs that Explain their Work" by
[Wilmer Ricciotti](http://www.wilmer-ricciotti.net/),
[Jan Stolarek](http://ics.p.lodz.pl/~stolarek),
[Roly Perera](http://www.dcs.gla.ac.uk/~roly/) and
[James Cheney](http://homepages.inf.ed.ac.uk/jcheney/), published at
[International Conference on Functional Programming 2017](http://icfp17.sigplan.org).
Upstream source code repository is located at
[https://github.com/jstolarek/slicer](https://github.com/jstolarek/slicer).


Requirements
============

This software is written in Haskell.  To build and install it you will need GHC
8.10 or above (some lower versions might work but were not tested) and a typical
Haskell infrastructure (Cabal, access to Hackage).


Installation
============

```
git clone https://github.com/jstolarek/slicer
cd slicer
cabal build
```

ICFP 2017 version
-----------------

To run the exact version published at ICFP 2017 checkout the relevant tag and
follow a README there:

```
git checkout icfp2017-final
```

**Note:** you will need GHC 8.0 and legacy Cabal.


Usage
=====

After following the above steps the slicer executable will be located at
`dist-newstyle/build/$ARCH/$GHC-VER/slicer-1.0.0.0/x/slicer/build/slicer/slicer`
where `$ARCH` is your system architecture (e.g. `x86_64-linux`) and `$GHC-VER`
is your GHC version (e.g. `ghc-9.0.1`).  For ease of use it's best to create a
symlink to the executable, e.g.:

```
ln -s dist-newstyle/build/x86_64-linux/ghc-9.0.1/slicer-1.0.0.0/x/slicer/build/slicer/slicer slicer
```

Example TML programs are located in `examples` sub-directory.  You can run them
by passing file name on the command line:

```
$ ./slicer examples/icfp17-example.tml
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
$ ./slicer --repl
Welcome to Slicer REPL
slicer>
```

You can interact with REPL by providing single-line declarations and
expressions:

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
cabal build
cabal test
```

The test suite will run every program in `examples` directory and compare its
output with the expected output stored in a corresponding `*.golden` file inside
`tests/golden-templates/`.

**Note:** tests hardcode the executable path, which includes a particular
version of GHC.  See `SlicerTestSuiteUtils.slicerPath` - you might have to
adjust it on your machine.


Running the benchmarks
----------------------

You can run benchmarks with:

```
cabal build
cabal bench
```


Reproducing examples from the paper
===================================

In the paper we have discussed several examples.  These are all located as
source files inside `examples/` directory.

1. On the first page of the paper we present a following example:

   ```ml
   let f(x) = if (x == 0) then y := 6 * !z else (y := 84 / !z; w := g(!y + 12)) in
   try f 0 with x => y := 42);; !y
   ```

   This example can be found in file `icfp17-example.tml`.  Run it with:

   ```
   $ ./slicer examples/icfp17-example.tml
   ```

   You can tweak initial value of `z` and the value of argument passed to `f` to
   obtain different results.  Remember that you must change the slicing
   criterion to match the obtained result.  So for example if you change initial
   value of `z` to be `0` rather than `7` you need to change the slicing
   criterion from `42` to `0`.  If you remove the `try`-`with` exception handler
   and modify the code to cause division by zero the slicing criterion should be
   `raise "Division by zero"`.

2. On the third page of the paper we present a more elaborate example containing
   a usage of `map`.  This example can be found in `icfp17-example2.tml` source
   file.  Run it with:

   ```
   $ ./slicer examples/icfp17-example2.tml
   ```

3. In section 6 we discuss an iTML program that solves a system of linear
   equations by using simple Gaussian elimination without pivoting.  This
   program can be found in `gauss.tml` source file (its pretty-printed version
   can be found in Appendix C in the extended version of the paper).  Run it
   with:

   ```
   $ ./slicer examples/gauss.tml
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

Syntax of iTML is based on ML.  Here are some basic information that should get
you started:

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
`lib/Language/Slicer/` you will find these modules:

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
