TODOs
=====

  * Delete trace var and trace update

  * eliminate string typing in Absyn/Desugar/Trace

  * why seq is used so much in the code? Performance?

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

  * Examples2 shold definitely be salvaged:

    * it should be built as part of normal compilation process or as part of
      testing to make sure that the code does not bitrot

    * it seems that PrettyPrinting and LaTeX modules are used only in this
      module.  So it look like I can remove them from the main appliaction

    * A bunch of ideas how to deal with this situation:

      * create a separate `utils` directory and store the code there.  Define it
        as a separate executable to be built in the build process.

      * perhaps convert Slicer to a library?  This could perhaps allow to avoid
        double compilation?

  * Separate the code into library and executable?

  * Comments not allowed to begin a file

  * try a stronger embedding with GADTs?  See Valuable type class in Trace
