TODOs
=====

  * eliminate string typing in Absyn/Desugar/Trace

  * implement proper error handling so tha REPL doesn't blow in my face every
    time something goes wrong

  * parseIn and parseRepl should handle errors in the same way

  * Document REPL

  * Move all the modules into the Slicer namespace.  Incremental strategy
    probably deserves its own namespace.  Absyn can have a better name

  * Finish reading the paper

  * figure out what to do with Examples.  Perhaps place it in tests directory as
    a ByHand test?

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
