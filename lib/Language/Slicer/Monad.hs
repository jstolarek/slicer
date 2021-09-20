module Language.Slicer.Monad
    ( -- * Slicer monad
      SlM, runSlM
    ) where

import           Language.Slicer.Error

import           Control.Monad.Except
import           Data.Functor.Identity

-- | Error monad
type SlM a = Except SlicerError a

runSlM :: Monad m => SlM a -> m (Either SlicerError a)
runSlM = return . runIdentity . runExceptT

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
--
-- Error reporting is the only effect common to all three stages.
--
--
-- DON'T SHOOT YOURSELF IN THE FOOT
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Most mistakes in using monad transformers and related combinators will simply
-- not type check.  But there is still a way to write erroneous code that
-- actually runs and does not do what you intended.  Say we have a computation
-- inside SlM monad:
--
--   foo :: SlM Bool
--   foo = return True
--
-- Suppose we want to run that computation inside EvalM monad, returning a unit
-- if the computations succeed and propagating any errors that are raised.  If
-- we write:
--
--   bar :: EvalM ()
--   bar = runSlM foo >> return ()
--
-- then this code will compile but will not work as intended.  Instead of
-- propagating errors, usage of `>>` will simply discard ANY result returned by
-- foo - successful on not - and thus `bar` will always return a unit.  The
-- problem is caused by using `runSlM` instead of `lift`.  So the correct
-- version of `bar` is:
--
--   bar :: EvalM ()
--   bar = lift foo >> return ()
--
