{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Slicer.Error
    ( -- * Raising errors
      SlicerError(..), parseError, desugarError, resugarError, evalError
    , typeError
    ) where

import           Control.DeepSeq               ( NFData     )
import           Control.Monad.Except
import           GHC.Generics                  ( Generic    )

-- | Error types that the program can raise
data SlicerError = ParseError   String
                 | DesugarError String
                 | ResugarError String
                 | TypeError String
                 | EvalError String
                   deriving (Eq, Generic, NFData)

instance Show SlicerError where
    show (ParseError     msg  ) = "Syntax error: " ++ msg
    show (EvalError      msg  ) = "Evaluation error: " ++ msg
    show (DesugarError   msg  ) = "Desugaring error: " ++ msg
    show (ResugarError   msg  ) = "Resugaring error: " ++ msg
    show (TypeError      msg  ) = "Type error: " ++ msg

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
