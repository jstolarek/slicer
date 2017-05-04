Slicer
======

[![Build Status](https://travis-ci.org/jstolarek/slicer.svg?branch=master)](https://travis-ci.org/jstolarek/slicer)

This repository contains companion code for paper "Imperative Functional
Programs that Explain their Work" by Wilmer Ricciotti,
[Jan Stolarek](http://ics.p.lodz.pl/~stolarek),
[Roly Perera](http://www.dcs.gla.ac.uk/~roly/) and
[James Cheney](http://homepages.inf.ed.ac.uk/jcheney/),
published at [International Conference on Functional Programming
2017](http://icfp17.sigplan.org).


Requirements
============

This software is written in Haskell.  To build and install it you will need GHC
8.0 or newer and typical Haskell infrastructure (Cabal, access to Hackage).


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


Running test programs
=====================

After following the above steps the slicer executable will be located at
`dist/build/slicer/slicer`.  Example TML programs are located in `examples`
sub-directory.  You can run them with:

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
