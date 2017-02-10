{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Slicer.Error
    ( -- * Raising errors
      SlicerError(..), parseError, desugarError, resugarError, evalError
    , typeError, raise, rethrow
    ) where

import           Language.Slicer.Core

import           Control.DeepSeq               ( NFData     )
import           Control.Monad.Except
import qualified Data.IntMap as M
import           GHC.Generics                  ( Generic    )

-- | Error types that the program can raise
data SlicerError = ParseError   String
                 | DesugarError String
                 | ResugarError String
                 | TypeError String
                 | EvalError String
                 | Exception Value (M.IntMap Value)
                   deriving (Eq, Generic, NFData)

instance Show SlicerError where
    show (ParseError   msg) = "Syntax error: " ++ msg
    show (EvalError    msg) = "Evaluation error: " ++ msg
    show (DesugarError msg) = "Desugaring error: " ++ msg
    show (ResugarError msg) = "Resugaring error: " ++ msg
    show (TypeError    msg) = "Type error: " ++ msg
    show (Exception    v _) = "Uncaught exception: " ++ show v

parseError :: MonadError SlicerError m => String -> m a
parseError msg = throwError (ParseError msg)

desugarError :: MonadError SlicerError m => String -> m a
desugarError msg = throwError (DesugarError msg)

resugarError :: MonadError SlicerError m => String -> m a
resugarError msg = throwError (ResugarError msg)

typeError :: MonadError SlicerError m => String -> m a
typeError msg = throwError (TypeError msg)

evalError :: MonadError SlicerError m => String -> m a
evalError msg = throwError (EvalError msg)

raise :: MonadError SlicerError m => Value -> M.IntMap Value -> m a
raise val st = throwError (Exception val st)

rethrow :: MonadError SlicerError m => SlicerError -> m a
rethrow = throwError
