{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Eval
    ( -- * Evaluation monad
      EvalM, runEvalM, liftEvalM, getEnv, withEnv, withBinder
    ) where

import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad

import           Control.Monad.Except
import           Control.Monad.State.Strict

-- | Monad for evaluation.  Stacks several monads:
--
--   * Except - to raise errors
--
--   * State  - to access and modify variables in scope
--
--   * IO     - to perform side effects
--
-- Note that the state is parameterized.
type EvalM a = StateT (EvalState a) (ExceptT SlicerError IO)

-- See Note [Monad transformers bog]

-- | State of the evaluation monad: environment ρ.  Stores variable values
data EvalState a = EvalState { envS :: Env a }

-- | Run the evaluation monad with a supplied environment.  Return result inside
-- an error monad.
runEvalM :: Env env -> EvalM env value -> SlMIO value
runEvalM env m = evalStateT m (EvalState env)

-- | Lift monadic action from SlM to EvalM.
liftEvalM :: SlM value -> EvalM env value
liftEvalM slm = lift (liftSlM slm)

-- | Get the environment
getEnv :: EvalM env (Env env)
getEnv = do
  EvalState { envS } <- get
  return envS

-- | Run monadic evaluation with extra binder in scope
withBinder :: Var -> env -> EvalM env value -> EvalM env value
withBinder var val thing = do
  env <- getEnv
  lift (evalStateT thing (EvalState (bindEnv env var val)))

-- | Run monadic evaluation inside a given environment
withEnv :: Env env -> EvalM env value -> EvalM env value
withEnv env thing =
  lift (evalStateT thing (EvalState env))
