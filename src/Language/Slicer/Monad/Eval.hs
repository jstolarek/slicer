{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Eval
    ( -- * Evaluation monad
      EvalM, EvalState(..), runEvalM, evalEvalM, liftEvalM
    , emptyEvalState, addBinding

    -- * Variable environment
    , getEnv, withEnv, withBinder

    -- * References
    , newRef, getRef, updateRef
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad

import           Control.Monad.Except
import           Control.Monad.State.Strict
import qualified Data.IntMap as M

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

-- | State of the evaluation monad
data EvalState a = EvalState
    { envS     :: Env a      -- ^ Environment ρ, stores variable values
    , refCount :: Int        -- ^ Reference counter
    , refs     :: M.IntMap a -- ^ Reference store
    }

-- | Run the evaluation monad with a supplied state.  Return result and final
-- state inside an error monad.
runEvalM :: EvalState env -> EvalM env value -> SlMIO (value, EvalState env)
runEvalM st m = runStateT m st

-- | Run the evaluation monad with a supplied state.  Return result inside an
-- error monad.
evalEvalM :: Env env -> EvalM env value -> SlMIO value
evalEvalM st m = evalStateT m (addEmptyStore st)

-- | Construct empty EvalState
emptyEvalState :: EvalState a
emptyEvalState = EvalState emptyEnv 0 M.empty

-- | Constructs evaluation state containing a given environment and an empty
-- reference store
addEmptyStore :: Env a -> EvalState a
addEmptyStore env = EvalState env 0 M.empty

-- | Add variable binding to environment
addBinding :: EvalState a -> Var -> a -> EvalState a
addBinding st var val =
    let env = envS st
    in st { envS = updateEnv env var val }

-- | Lift monadic action from SlM to EvalM.
liftEvalM :: SlM value -> EvalM env value
liftEvalM slm = lift (liftSlM slm)

-- | Get the environment
getEnv :: EvalM env (Env env)
getEnv = do
  EvalState { envS } <- get
  return envS

-- | Set the environment
setEnv :: Env env -> EvalM env ()
setEnv env = do
  st <- get
  put $ st { envS = env }

-- | Allocates a new reference number
newRef :: env -> EvalM env Value
newRef val = do
  st@(EvalState { refCount, refs }) <- get
  let newRefs = M.insert refCount val refs
  put $ st { refCount = refCount + 1, refs = newRefs }
  return (VStoreLoc refCount)

getRef :: Value -> EvalM env env
getRef (VStoreLoc l) = do
  EvalState { refs } <- get
  case M.lookup l refs of
    Just ref -> return ref
    Nothing  -> evalError "Cannot read reference: not allocated"
getRef v = evalError ("Not a reference value: " ++ show v)

updateRef :: Value -> env -> EvalM env ()
updateRef (VStoreLoc l) val = do
  st@(EvalState { refs }) <- get
  unless (l `M.member` refs) $ evalError "Cannot update reference: not allocated"
  put $ st { refs = M.insert l val refs }

updateRef v _ = evalError ("Not a reference value: " ++ show v)

-- | Run monadic evaluation with extra binder in scope
withBinder :: Var -> env -> EvalM env value -> EvalM env value
withBinder var val thing = do
  env    <- getEnv
  withEnv (bindEnv env var val) thing

-- | Run monadic evaluation inside a given environment
withEnv :: Env env -> EvalM env value -> EvalM env value
withEnv newEnv thing = do
  oldEnv <- getEnv
  setEnv newEnv
  result <- thing
  setEnv oldEnv -- See Note [Store does not shrink]
  return result

-- Note [Store does not shrink]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- It is important to remember that while scope (environment) can grow and
-- shrink during execution, the reference store can only grow.  The
-- withBinder/withEnv functions save the original environment, extend the
-- environbment as requested, run the computations (possibly allowing them to
-- grow the store) and restore original environment.  Thus the environment
-- shrinks, but the store modified by execution of the "thing" remains.
