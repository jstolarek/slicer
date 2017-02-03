References
==========

How is Lattice defined for new refrence constructs?  How do I take their lub?
Is this a straightforward extension?

How to implement `match` (`Pattern` type class) for `VStoreLoc`?

I don't understand how store works in the slicing rules for references.  When
slicing, when are values allocated to the store?

Shouldn't we have rules for typing and evaluating reference traces?

We need a constructor for tracing dereferences.  That constructor needs to
record a label that is being dereferenced - cf. U-DEREF rule in the paper.

Does "B.4 Backward slicing" section describe program slicing or trace slicing?
I think the latter.


Inconsistencies
===============

  * there is no way to access program slice.  A hacky way of doing this is to
    modify `evalTraceOp` and add `liftIO $ putStrLn (show (pp t'))`.

  * there is no way to evaluate a trace, although we specifically define trace
    evaluation rules.


Resugaring notes
================

Notes below were made assuming that expressions and traces have a common AST.  I
haven't thought much how resugaring will be affected by separating expressions
and traces into separate syntax trees.


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
