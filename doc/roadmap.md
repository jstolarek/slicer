TODOs
=====

  * Create export lists

  * Parser cleanup

  * Fix test failures.  In the process of doing this I can perhaps figure out a
    hierarchical organisation of tests, eg. ctrace tests could go into their own
    group.  I could then disable a group of tests if I know they don't work.
    This requires adapting more of singletons infrastructure.

  * Run tests for incremental evaluation

  * eliminate string typing in Absyn/Desugar/Core

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

  * it seems that functionality in Util module can be implemented differently
    and the whole module can then be removed:

    * replace Util.P by State from Control.Monad.State

    * replace Util.eq with assert from Control.Exception.Base

    * move PP class and sb function into PrettyPrinting module

  * Separate the code into library and executable?
