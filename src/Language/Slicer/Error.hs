{-# LANGUAGE FlexibleContexts #-}

module Language.Slicer.Error
    ( -- * Raising errors
      SlicerError, parseError, desugarError, evalError, typeError
    ) where

import           Control.Monad.Except
import           Text.ParserCombinators.Parsec ( ParseError )

-- | Error types that the program can raise
data SlicerError = ParseError ParseError
                 | DesugarError String
                 | TypeError String
                 | EvalError String
                   deriving (Eq)

instance Show SlicerError where
    show (ParseError   msg) = "Syntax error: " ++ show msg
    show (EvalError    msg) = "Evaluation error: " ++ msg
    show (DesugarError msg) = "Desugaring error: " ++ msg
    show (TypeError    msg) = "Type error: " ++ msg

parseError :: MonadError SlicerError m => ParseError -> m a
parseError msg = throwError (ParseError msg)

desugarError :: MonadError SlicerError m => String -> m a
desugarError msg = throwError (DesugarError msg)

typeError :: MonadError SlicerError m => String -> m a
typeError msg = throwError (TypeError msg)

evalError :: MonadError SlicerError m => String -> m a
evalError msg = throwError (EvalError msg)
