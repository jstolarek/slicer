TODOs
=====

  * eliminate string typing in Absyn/Desugar/Trace

  * evalTraceOp is a disaster

  * implement proper error handling so tha REPL doesn't blow in my face every
    time something goes wrong.  Idea: create Error module with ErrorM monad,
    then each pass is done in its own separate monad that is just a synonym for
    ErrorM.

  * parseIn and parseRepl should handle errors in the same way

  * Document REPL

  * Represent program as a series of expressions rather than as a single
    expression.  This should allow to have better performance as desuagring and
    evaluation of lets would be tail-recursive.  While I'm at it, change the
    syntax of let-statements to store a series of binds.

  * Add benchmarks?

  * Make the code strict

  * Implement resugaring. Currently resugaring and pretty-printing are combined
    into one pass.  It would be better to have a resugaring pass that restores
    original surface syntax and then we could pretty-print that syntax.

  * Move all the modules into the Slicer namespace.  Incremental strategy
    probably deserves its own namespace.  Absyn can have a better name

  * Finish reading the paper

  * Separate the code into library and executable?

  * Comments not allowed to begin a file

  * try a stronger embedding with GADTs?  See Valuable type class in Trace
