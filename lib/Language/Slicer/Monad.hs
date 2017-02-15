module Language.Slicer.Monad
    ( -- * Slicer monad
      SlM, SlMIO, runSlMIO, liftSlM
    ) where

import           Language.Slicer.Error

import           Control.Monad.Except
import           Data.Functor.Identity

-- | Error monad
type SlM   a = Except  SlicerError     a

-- | Error monad on top of IO
type SlMIO a = ExceptT SlicerError IO  a

-- | Run error monad and return an Either inside IO
runSlMIO :: MonadIO m => SlMIO a -> m (Either SlicerError a)
runSlMIO = liftIO . runExceptT

-- | Lift error monad into IO
liftSlM :: SlM a -> SlMIO a
liftSlM slm = ExceptT $ return (runIdentity (runExceptT slm))

-- Note [Monad transformers bog]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Running a TML program consists of three stages, and each of these stages
-- requires different monadic effects:
--
--   * parsing : requires error reporting.  (Parsec handles errors under the
--               hood and returns parsing result as an Either.  We still want to
--               have our own error reporting so that we have a uniform
--               treatment of errors in all three stages of compilation.)
--
--   * desugaring : requires error reporting, reading an immutable environment
--                  of data declarations and having access to a mutable state to
--                  store the context (variables visible in scope and their
--                  types)
--
--   * evaluation : requires error reporting, mutable state to store the
--                  environment (variables visible in scope and their values)
--                  and side effects (IO)
--
-- Error reporting is the only effect common to all three stages.  The problem
-- is that in case of evaluation we need to build error reporting on top of IO
-- monad.  This means we have two monads:
--
--   * SlM - plain error reporting
--
--   * SlMIO - error reporting inside IO
--
-- When running all three compilation stages at once we will need to lift
-- parsing and desugaring (performed inside SlM) into the SlMIO monad (built on
-- top of IO to enable evaluation).  This is done using liftSlM.  So, a rule of
-- thumb:
--
--    Use liftSlM on parsing and desugaring when running inside SlMIO
--
-- SlM monad suffices to run parsing.  To run desugaring and evaluation we need
-- monads that stack all the required effects.  What is important is that when
-- we run these monads we need to return the result inside an error monad (SlM
-- for desugaring, SlMIO for evaluation).  This allows to run the computations
-- sequentially inside an SlMIO monad.  The only moment we want to exit the
-- SlM/SlMIO monad is at the very top level of the compilation pipeline,
-- ie. either in the Main or Repl module.
--
--
-- DON'T SHOOT YOURSELF IN THE FOOT
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Most mistakes in using monad transformers and related combinators will simply
-- not type check.  But there is still a way to write erroneous code that
-- actually runs and does not do what you intended.  Say we have a computation
-- inside SlMIO monad:
--
--   foo :: SlMIO Bool
--   foo = return True
--
-- Suppose we want to run that computation inside EvalM monad, returning a unit
-- if the computations succeed and propagating any errors that are raised.  If
-- we write:
--
--   bar :: EvalM ()
--   bar = runSlMIO foo >> return ()
--
-- then this code will compile but will not work as intended.  Instead of
-- propagating errors, usage of `>>` will simply discard ANY result returned by
-- foo - successful on not - and thus `bar` will always return a unit.  The
-- problem is caused by using `runSlMIO` instead of `lift`.  So the correct
-- version of `bar` is:
--
--   bar :: EvalM ()
--   bar = lift foo >> return ()
--
