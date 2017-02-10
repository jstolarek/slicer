{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Desugar
    ( DesugarM, runDesugarM, getGamma, getDecls
    , withGamma, withBinder, maybeWithBinder
    , pushExnType, popExnType
    ) where

import qualified Language.Slicer.Absyn as A
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad  ( SlM )

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict

-- | Monad for desugaring.  Stacks several monad transformers:
--
--   * Except - to raise errors
--
--   * Reader - to access data declarations environment
--
--   * State  - to access and modify variables in scope
type DesugarM = StateT DesugarState (ReaderT A.TyCtx (Except SlicerError))

-- See Note [Monad transformers bog]

-- | State of the desugaring monad
data DesugarState = DesugarState
    { gammaS  :: Ctx        -- ^ Context Γ.  Stores variable types.
    , exnType :: Maybe Type -- ^ Type of raised exception
    }

-- | Run desugaring monad with supplied data decarations and variables in scope
runDesugarM :: A.TyCtx -> Ctx -> DesugarM a -> SlM a
runDesugarM decls gamma m
    = runReaderT (evalStateT m (DesugarState gamma Nothing)) decls

-- | Get the context
getGamma :: DesugarM Ctx
getGamma = do
  DesugarState { gammaS } <- get
  return gammaS

-- | Get data declarations in scope
getDecls :: DesugarM A.TyCtx
getDecls = ask

pushExnType :: Type -> DesugarM ()
pushExnType ty = do
  st@(DesugarState { exnType })<- get
  when (exnType == Nothing) (put (st { exnType = Just ty }))

popExnType :: DesugarM (Maybe Type)
popExnType = do
  st@(DesugarState { exnType }) <- get
  put (st { exnType = Nothing })
  return exnType

getExnType :: DesugarM (Maybe Type)
getExnType = do
  DesugarState { exnType } <- get
  return exnType

-- | Run monadic desugaring with extra binder in scope
withBinder :: Var -> Type -> DesugarM a -> DesugarM a
withBinder var ty thing = do
  gamma <- getGamma
  exn   <- getExnType
  lift (evalStateT thing (DesugarState (bindEnv gamma var ty) exn))

-- | Run monadic desugaring, maybe with extra binder in scope
maybeWithBinder :: Maybe Var -> Type -> DesugarM a -> DesugarM a
maybeWithBinder (Just var) ty thing = withBinder var ty thing
maybeWithBinder Nothing _     thing = thing

-- | Run monadic desugaring inside a given context
withGamma :: Ctx -> DesugarM a -> DesugarM a
withGamma ctx thing = do
  exn   <- getExnType
  lift (evalStateT thing (DesugarState ctx exn))
