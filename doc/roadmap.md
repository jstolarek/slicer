TODOs
=====

  * Things in annot shold run in a monad

  * catalogue removed features in a file

  * Implement resugaring. Currently resugaring and pretty-printing are combined
    into one pass.  It would be better to have a resugaring pass that restores
    original surface syntax and then we could pretty-print that syntax.

  * Finish reading the paper

  * Represent program as a series of expressions rather than as a single
    expression.  This should allow to have better performance as desuagring and
    evaluation of lets would be tail-recursive.  While I'm at it, change the
    syntax of let-statements to store a series of binds.

  * Add benchmarks?

  * Make the code strict?

  * Separate the code into library and executable?

  * Comments not allowed to begin a file

  * try a stronger embedding with GADTs?  See Valuable type class in Trace


Questions
=========

I am confused by `bslice`/`pslice`/`uneval`.  Does section 4.3 of the ICFP paper
describe `blsice` or `pslice`.

`pslice` reconstructs programs, but:

  * I don't understand how it reconstructs if-expressions, ie. how it figures
    out whether just one or both branches of an if are used

  * there is no way to access program slice.  A hacky way of doing this is to
    modify `evalTraceOp` and add `liftIO $ putStrLn (show (pp t'))`.

  * I don't understand how reconstruction of `Call` works (the last two `let`
    bindings).

  * I don't understand the way environments are handles in the `Let` case

`uneval` seems to do the same as `pslice` in a much simpler way.

Isn't the `extract` functions from `Pattern` type class just a greatest lower
bound?

I don't understand how `slice` primitvie is handled - why call `extract` there?
Isn't it the case here that *if* `p <= v` then the result of extract will be `p`
(module VStar)?  Moreover, `bslice` seems to do exactly the same thing,
ie. prunning branches in the expresson tree that correspond to a hole in the
slicing criterion.

How do I say `VStar` in the source code?

Performance: issues with "reverse" tests.


Resugaring notes
================

### Differences in type language

Core language has two extra types not present in the surface language: `RecTy`
and `HoleTy`.  RecTy should be simple to handle, but there is nothing
corresponding to `HoleTy` in the current surface language.


### Differences in expression language

  * surface language has two types of let bindings (one for normal programs,
    another for REPL), core language has just one.  I guess it is safe to always
    desugar to the first type of let bindings.

  * surface language uses explicit constructors, whereas core language uses InL
    and InR.  Again, this should be simple given the access to the context (data
    type definitions) during desugaring.

  * Functions in core are curried (always one argument).  Need to implement
    uncurrying.

  * Core language has explicit Roll/Unroll.  Need to figure out how to eliminate
    those.

  * Core language has several different trace forms, surface only has one
    constructor for runtime tracing

  * Holes in surface language are explicitly typed
