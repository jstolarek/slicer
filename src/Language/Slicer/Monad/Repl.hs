{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Repl
    ( ReplM, runRepl, getTyCtx, getGamma, getEvalState, setEvalState
    , addDataDefn, addBinding
    ) where

import           Language.Slicer.Absyn
import qualified Language.Slicer.Core as C         ( Value, Type              )
import           Language.Slicer.Env
import           Language.Slicer.Monad.Eval hiding ( addBinding, getEvalState
                                                   , setEvalState             )
import qualified Language.Slicer.Monad.Eval as E   ( addBinding               )

import           Control.Monad.State.Strict

-- | REPL monad contains a state on top of IO
type ReplM = StateT ReplState IO

-- | REPL state
data ReplState = ReplState
    { tyCtxS :: TyCtx             -- ^ Data type declarations
    , gammaS :: Env C.Type        -- ^ Context Γ, stores variable types
    , evalS  :: EvalState C.Value -- ^ Evaluation monad state. Contains
                                  --   environment ρ (variable values) and
                                  --   reference store
    }

-- | Empty REPL state.  Used when starting the REPL
emptyState :: ReplState
emptyState = ReplState { tyCtxS = emptyTyCtx
                       , gammaS = emptyEnv
                       , evalS  = emptyEvalState }

-- | Get data type declarations
getTyCtx :: ReplM TyCtx
getTyCtx = do
  ReplState { tyCtxS } <- get
  return tyCtxS

-- | Get context
getGamma :: ReplM (Env C.Type)
getGamma = do
  ReplState { gammaS } <- get
  return gammaS

-- | Get environment
getEvalState :: ReplM (EvalState C.Value)
getEvalState = do
  ReplState { evalS } <- get
  return evalS

setEvalState :: EvalState C.Value -> ReplM ()
setEvalState newEvalSt = do
  replState <- get
  put $ replState { evalS = newEvalSt }

-- | Add new data definition
addDataDefn :: TyCtx -> ReplM ()
addDataDefn newCtx = do
  st@(ReplState { tyCtxS }) <- get
  put $ st { tyCtxS = unionTyCtx tyCtxS newCtx }

-- | Add new binding (name + value + type)
addBinding :: Var -> C.Value -> C.Type -> ReplM ()
addBinding var val ty = do
  replState@(ReplState { evalS, gammaS }) <- get
  let evalS'   = E.addBinding evalS var val
      newGamma = updateEnv gammaS var ty
  put $ replState { evalS = evalS', gammaS = newGamma }

-- | Run REPL monad
runRepl :: ReplM () -> IO ()
runRepl repl = evalStateT repl emptyState
