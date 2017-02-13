{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Eval
    ( -- * Evaluation monad
      EvalM, EvalState(..), runEvalM, evalEvalM, liftEvalM
    , emptyEvalState, getEvalState, setEvalState, getStore, setStore, addBinding

    -- * Variable environment
    , getEnv, withEnv, withBinder, maybeWithBinder

    -- * References
    , newRef, getRef, updateRef
    ) where

import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad

import           Control.DeepSeq               ( NFData     )
import           Control.Monad.Except
import           Control.Monad.State.Strict
import qualified Data.IntMap as M
import           GHC.Generics                  ( Generic    )

-- | Monad for evaluation.  Stacks several monads:
--
--   * Except - to raise errors
--
--   * State  - to access and modify variables in scope
--
--   * IO     - to perform side effects
--
type EvalM = StateT EvalState (ExceptT SlicerError IO)

-- See Note [Monad transformers bog]

-- | State of the evaluation monad
data EvalState = EvalState
    { envS     :: Env Value      -- ^ Environment ρ, stores variable values
    , refCount :: Int            -- ^ Reference counter
    , refs     :: M.IntMap Value -- ^ Reference store
    } deriving (Eq, Ord, Generic, NFData)

-- | Run the evaluation monad with a supplied state.  Return result and final
-- state inside an error monad.
runEvalM :: EvalState -> EvalM value -> SlMIO (value, EvalState)
runEvalM st m = runStateT m st

-- | Run the evaluation monad with a supplied state.  Return result inside an
-- error monad.
evalEvalM :: Env Value -> EvalM value -> SlMIO value
evalEvalM st m = evalStateT m (addEmptyStore st)

-- | Construct empty EvalState
emptyEvalState :: EvalState
emptyEvalState = EvalState emptyEnv 0 M.empty

-- | Get current evaluation state
getEvalState :: EvalM EvalState
getEvalState = get

-- | Set evaluation state
setEvalState :: EvalState -> EvalM ()
setEvalState = put

-- | Get current reference store
getStore :: EvalM (M.IntMap Value)
getStore = do
  EvalState { refs } <- get
  return refs

-- | Set reference store
setStore :: M.IntMap Value -> EvalM ()
setStore store = do
    env <- getEnv
    put (EvalState env (M.size store) store)

-- | Constructs evaluation state containing a given environment and an empty
-- reference store
addEmptyStore :: Env Value -> EvalState
addEmptyStore env = EvalState env 0 M.empty

-- | Add variable binding to environment
addBinding :: EvalState -> Var -> Value -> EvalState
addBinding st var val =
    let env = envS st
    in st { envS = updateEnv env var val }

-- | Lift monadic action from SlM to EvalM.
liftEvalM :: SlM value -> EvalM value
liftEvalM slm = lift (liftSlM slm)

-- | Get the environment
getEnv :: EvalM (Env Value)
getEnv = do
  EvalState { envS } <- get
  return envS

-- | Set the environment
setEnv :: Env Value -> EvalM ()
setEnv env = do
  st <- get
  put $ st { envS = env }

-- | Allocates a new reference number
newRef :: Value -> EvalM Value
newRef val = do
  st@(EvalState { refCount, refs }) <- get
  let newRefs = M.insert refCount val refs
  put $ st { refCount = refCount + 1, refs = newRefs }
  return (VStoreLoc refCount)

getRef :: Value -> EvalM Value
getRef (VStoreLoc l) = do
  EvalState { refs } <- get
  case M.lookup l refs of
    Just ref -> return ref
    Nothing  -> evalError "Cannot read reference: not allocated"
getRef v = evalError ("Not a reference value: " ++ show v)

updateRef :: Value -> Value -> EvalM ()
updateRef (VStoreLoc l) val = do
  st@(EvalState { refs }) <- get
  unless (l `M.member` refs) $ evalError "Cannot update reference: not allocated"
  put $ st { refs = M.insert l val refs }

updateRef v _ = evalError ("Not a reference value: " ++ show v)

-- | Run monadic evaluation with extra binder in scope
withBinder :: Var -> Value -> EvalM value -> EvalM value
withBinder var val thing = do
  env    <- getEnv
  withEnv (bindEnv env var val) thing

-- | Run monadic evaluation, maybe with extra binder in scope
maybeWithBinder :: Maybe Var -> Value -> EvalM value -> EvalM value
maybeWithBinder (Just var) val thing = withBinder var val thing
maybeWithBinder Nothing    _   thing = thing

-- | Run monadic evaluation inside a given environment
withEnv :: Env Value -> EvalM value -> EvalM value
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
