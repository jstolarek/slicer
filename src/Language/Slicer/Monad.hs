module Language.Slicer.Monad
    ( -- * Slicer monad
      SlM, runSlM, SlicerError

      -- * Raising errors
    , parseError, desugarError, evalError, typeError
    ) where

import           Control.Monad.Except
import           Text.ParserCombinators.Parsec (ParseError)

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

-- | Monad in which we perform parsing, desugaring and evaluation.  This is
-- essentially an Either monad stacked on top of IO.  The reason we stack on IO
-- is because our language is side-effecting and evaluation will include running
-- some side-effecting commands
type SlM = ExceptT SlicerError IO

-- | Run compiler monad inside an IO monad
runSlM :: MonadIO m => SlM a -> m (Either SlicerError a)
runSlM = liftIO . runExceptT

parseError :: ParseError -> SlM a
parseError msg = throwError (ParseError msg)

desugarError :: String -> SlM a
desugarError msg = throwError (DesugarError msg)

typeError :: String -> SlM a
typeError msg = throwError (TypeError msg)

evalError :: String -> SlM a
evalError msg = throwError (EvalError msg)
