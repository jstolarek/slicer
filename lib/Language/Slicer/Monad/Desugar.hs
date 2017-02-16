{-# LANGUAGE NamedFieldPuns #-}

module Language.Slicer.Monad.Desugar
    ( DesugarM, runDesugarM, getGamma, getDecls
    , withGamma, withBinder, maybeWithBinder
    ) where

import qualified Language.Slicer.Absyn as A
import           Language.Slicer.Core
import           Language.Slicer.Env
import           Language.Slicer.Error
import           Language.Slicer.Monad  ( SlM )

import           Control.Arrow
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
    }

-- | Run desugaring monad with supplied data decarations and variables in scope
runDesugarM :: A.TyCtx -> Ctx -> DesugarM a -> SlM (a, Ctx)
runDesugarM decls gamma m
    = (second gammaS) `liftM` -- extract gammaS from DesugarState
      runReaderT (runStateT m (DesugarState gamma)) decls

-- | Get the context
getGamma :: DesugarM Ctx
getGamma = do
  DesugarState { gammaS } <- get
  return gammaS

-- | Get data declarations in scope
getDecls :: DesugarM A.TyCtx
getDecls = ask

-- | Run monadic desugaring with extra binder in scope
withBinder :: Var -> Type -> DesugarM a -> DesugarM a
withBinder var ty thing = do
  gamma <- getGamma
  lift (evalStateT thing (DesugarState (bindEnv gamma var ty)))

-- | Run monadic desugaring, maybe with extra binder in scope
maybeWithBinder :: Maybe Var -> Type -> DesugarM a -> DesugarM a
maybeWithBinder (Just var) ty thing = withBinder var ty thing
maybeWithBinder Nothing _     thing = thing

-- | Run monadic desugaring inside a given context
withGamma :: Ctx -> DesugarM a -> DesugarM a
withGamma ctx thing = do
  lift (evalStateT thing (DesugarState ctx))
